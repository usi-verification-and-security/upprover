/*******************************************************************\

Module: Wrapper for OpenSMT2. Based on satcheck_minisat.

Author: Grigory Fedyukovich

\*******************************************************************/

#include "satcheck_opensmt2.h"
#include "prop_itp.h"

#ifdef DISABLE_OPTIMIZATIONS
#include <fstream>
#include <iostream>
#include "../hifrog.h"
#endif

void satcheck_opensmt2t::initializeSolver(const char* name)
{
    osmt = new Opensmt(opensmt_logic::qf_bool, name);
    logic = &(osmt->getLogic());
    mainSolver = &(osmt->getMainSolver());
    const char* msg=NULL;
    osmt->getConfig().setOption(SMTConfig::o_produce_inter, SMTOption(true), msg);
    //if (msg != NULL) free((char *)msg); // if finds an error consider to print it
}

// Free all resources related to OpenSMT2
void satcheck_opensmt2t::freeSolver()
{
    if (osmt != NULL) delete osmt;
}

/*******************************************************************\

Function: satcheck_opensmt2t::convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void satcheck_opensmt2t::convert(const bvt &bv, vec<PTRef> &args)
{
  for(unsigned i=0; i<bv.size(); i++) {
    const literalt& lit = bv[i];
    
    // we never use 'unused_var_no' (cnf.cpp)
    assert(lit.var_no()!=literalt::unused_var_no());

    PTRef var = ptrefs[lit.var_no()];

    if (lit.sign()) {
      args.push(logic->mkNot(var));
    } else {
      args.push(var);
    }
  }
}

/*******************************************************************\

Function: satcheck_opensmt2t::new_partition

  Inputs:

 Outputs: returns a unique partition id

 Purpose: Begins a partition of formula for latter reference during
 interpolation extraction. All assertions made until
 next call of new_partition() will be part of this partition.

\*******************************************************************/
fle_part_idt satcheck_opensmt2t::new_partition()
{
//Allowing partitions for havoced functions and fully slices ones

  assert(partition_count == 0 || current_partition != NULL);
  if (partition_count != 0 && current_partition == NULL) {
    std::cerr << "WARNING: last partition was empty (probably due to slicing)." << std::endl;
    // NOTE: The index is reused for the next partition, outer context must
    // ensure that the previously returned index is not used.
    partition_count--;
  }
  
  // Finish the previous partition if any
  if (current_partition != NULL)
    close_partition();

  current_partition = new vec<PTRef>();

  return partition_count++;
}

#ifdef PRODUCE_PROOF
void satcheck_opensmt2t::extract_itp(PTRef ptref,
  prop_itpt& target_itp) const
{
  ptref_cachet cache;
  target_itp.set_no_original_variables(_no_variables);
  target_itp.root_literal = extract_itp_rec(ptref, target_itp, cache);
}

literalt satcheck_opensmt2t::extract_itp_rec(PTRef ptref,
  prop_itpt& target_itp, ptref_cachet& ptref_cache) const
{
  ptref_cachet::const_iterator cached_it = ptref_cache.find(ptref);

  if (cached_it != ptref_cache.end()) {
    return cached_it->second;
  }

  literalt result;
  if(logic->getTerm_true() == ptref){
      result = const_literal(true);
  }
  else if(logic->getTerm_false() == ptref){
      result = const_literal(false);
  }
  else if(logic->isAnd(ptref))
  {
      Pterm& ptm = logic->getPterm(ptref);
      assert(ptm.size() >= 2);
      result = target_itp.land(
              extract_itp_rec(ptm[0], target_itp, ptref_cache),
              extract_itp_rec(ptm[1], target_itp, ptref_cache));
      for(int i = 2; i < ptm.size(); ++i)
          result = target_itp.land(result, extract_itp_rec(ptm[i], target_itp, ptref_cache));
  }
  else if(logic->isOr(ptref))
  {
      Pterm& ptm = logic->getPterm(ptref);
      assert(ptm.size() >= 2);
      result = target_itp.lor(
              extract_itp_rec(ptm[0], target_itp, ptref_cache),
              extract_itp_rec(ptm[1], target_itp, ptref_cache));
      for(int i = 2; i < ptm.size(); ++i)
          result = target_itp.lor(result, extract_itp_rec(ptm[i], target_itp, ptref_cache));
  }
  else if(logic->isNot(ptref))
  {
      Pterm& ptm = logic->getPterm(ptref);
      assert(ptm.size() == 1);
      result = target_itp.lnot(
              extract_itp_rec(ptm[0], target_itp, ptref_cache));
  }
  else
  {
      assert(logic->getPterm(ptref).size() == 0);
      result.set(decode_id(logic->getSymName(ptref)), false);
  } 
   
  // we never use 'unused_var_no' (cnf.cpp)
  assert(result.var_no()!=literalt::unused_var_no());
    
  ptref_cache.insert(ptref_cachet::value_type(ptref, result));
  return result;
}

// helper interpolation method taken from opensmt
void satcheck_opensmt2t::produceConfigMatrixInterpolants (const std::vector< std::vector<int> > &configs,
                                                          std::vector<PTRef> &interpolants)
{
  SimpSMTSolver& solver = osmt->getSolver();

  // First interpolant is true -> all partitions in B
  for ( unsigned i = 0; i < configs.size(); i++ )
  {
    ipartitions_t mask = 0;
    for (unsigned j = 0; j < configs[i].size(); j++)
    {
      // Set partitions[i] bit to 1 (starting from bit 1, bit 0 is untouched)
      setbit ( mask, configs[i][j] + 1);
    }

    solver.getSingleInterpolant(interpolants, mask);
  }
}

/*******************************************************************\

Function: satcheck_opensmt2t::get_interpolant

  Inputs:

 Outputs:

 Purpose: Extracts the symmetric interpolant of the specified set of
 partitions. This method can be called only after solving the
 the formula with an UNSAT result.

\*******************************************************************/
#ifdef PRODUCE_PROOF 
void satcheck_opensmt2t::get_interpolant(const interpolation_taskt& partition_ids,
    interpolantst& interpolants)
{
  assert(ready_to_interpolate);

  // Set labeling function
  //  const char* msg=NULL;
  //  osmt->getConfig().setOption(SMTConfig::o_itp_bool_alg, SMTOption(itp_algorithm), msg);
  //  osmt->getConfig().setOption(SMTConfig::o_itp_bool_alg, SMTOption(0), msg);
  //  if (msg != NULL) free((char *)msg);
  osmt->getConfig().setBooleanInterpolationAlgorithm(itp_algorithm);

  SimpSMTSolver& solver = osmt->getSolver();

  // Create the proof graph
  solver.createProofGraph();

  std::vector<PTRef> itp_ptrefs;

  // iterative call of getSingleInterpolant:
  produceConfigMatrixInterpolants(partition_ids, itp_ptrefs);

  solver.deleteProofGraph();

  for(auto itp_ptref : itp_ptrefs)
  {
      itpt* itp = new prop_itpt();
      extract_itp(itp_ptref, *(dynamic_cast <prop_itpt*> (itp)));
      interpolants.push_back(itp);
  }
}
#endif


/*******************************************************************\

Function: satcheck_opensmt2t::can_interpolate

  Inputs:

 Outputs:

 Purpose: Is the solver ready for interpolation? I.e., the solver was used to 
 decide a problem and the result was UNSAT

\*******************************************************************/
bool satcheck_opensmt2t::can_interpolate() const
{
  return ready_to_interpolate;
}
#endif

/*******************************************************************\

Function: satcheck_opensmt2t::l_get

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
tvt satcheck_opensmt2t::l_get(literalt a) const
{
  // we never use index 0 (cnf.cpp)
  assert(a.var_no()!=0);
    
  // we never use 'unused_var_no' (cnf.cpp)
  assert(a.var_no()!=literalt::unused_var_no());
    
  if (a.is_true())
    return tvt(true);
  else if (a.is_false())
    return tvt(false);

  ValPair a_p = mainSolver->getValue(ptrefs[a.var_no()]);
  lbool lresult = (*a_p.val == *true_str) ? l_True : l_False;

  tvt tvtresult(tvt::tv_enumt::TV_UNKNOWN);
  if (lresult == l_True)
    tvtresult = tvt(true);
  else if (lresult == l_False)
    tvtresult = tvt(false);
  else
    return tvtresult;

  if (a.sign())
    return !tvtresult;

  return tvtresult;
}

/*******************************************************************\

Function: satcheck_opensmt2t::solver_text

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

const std::string satcheck_opensmt2t::solver_text()
{
  return "OpenSMT2 (QF_BOOL)";
}

/*******************************************************************\

Function: satcheck_opensmt2t::add_variables

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void satcheck_opensmt2t::add_variables()
{
  ptrefs.reserve(_no_variables);

  while (ptrefs.size() < _no_variables) {
    increase_id();
    const char* vid = id_str.c_str();
    ptrefs.push_back(logic->mkBoolVar(vid));
  }
}

/*******************************************************************\

Function: satcheck_opensmt2t::lcnf

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void satcheck_opensmt2t::lcnf(const bvt &bv)
{
  bvt new_bv;
  if(process_clause(bv, new_bv))
   return;

// Shortcut for an empty clause
  if(new_bv.empty())
  {
    std::cerr << "WARNING: Outputing an empty clause -> most probably an error due to pointers." << std::endl;
    PTRef tmp = logic->getTerm_false();
    current_partition->push(tmp);
    return;
  }
//
  add_variables();
  vec<PTRef> or_args;
  convert(new_bv, or_args);

  current_partition->push(logic->mkOr(or_args));
  clause_counter++;
}

/*******************************************************************\

Function: satcheck_opensmt2t::prop_solve

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

propt::resultt satcheck_opensmt2t::prop_solve() {

#ifdef DISABLE_OPTIMIZATIONS   
  if (dump_queries){
    char *msg=NULL;
    mainSolver->writeSolverState_smtlib2("__SAT_query", &msg);
    if (msg != NULL) free(msg); // If there is an error consider printing the msg
  }
  
  // Print Pre-query to file
  if (dump_pre_queries) {
      ofstream out_sat_pre_query;
      out_sat_pre_query.open(pre_queries_file_name+"_"+std::to_string(get_dump_current_index())+".smt2");  
      
      // Print Header
      mainSolver->getLogic().dumpHeaderToFile(out_sat_pre_query);
      
      // Print body + ite's
      for(int i = 0; i < top_level_formulas.size(); ++i) {
        out_sat_pre_query << "; XXX Partition: " << (top_level_formulas.size() - i - 1) << '\n';
        char* s = logic->printTerm(top_level_formulas[i]);
        out_sat_pre_query << "(assert (and \n" << s << "\n))\n";
        free(s);
        s = NULL;
      }
      
      // Close the file
      out_sat_pre_query << "(check-sat)\n" << std::endl;
      out_sat_pre_query.close();
  } 
#endif 
  
  assert(status != statust::ERROR);
#ifdef PRODUCE_PROOF  
  ready_to_interpolate = false;
#endif
  
  if (current_partition != NULL) {
    close_partition();
  }

  for(int i = 0; i < top_level_formulas.size(); ++i) {
      char *msg=NULL;
      mainSolver->insertFormula(top_level_formulas[i], &msg);
      if (msg != NULL) { free(msg); msg = NULL;} 
      // If there is an error consider printing the msg
  }

  add_variables();

  sstat r = mainSolver->check();

  if (r == s_True) {
    status = statust::SAT;
    return resultt::P_SATISFIABLE;
  } else if (r == s_False) {
#ifdef PRODUCE_PROOF      
    ready_to_interpolate = true;
#endif
  } else {
    throw "Unexpected OpenSMT result.";
  }

  status = statust::UNSAT;
  return resultt::P_UNSATISFIABLE;
}

/*******************************************************************\

Function: satcheck_opensmt2t::set_assignment

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void satcheck_opensmt2t::set_assignment(literalt a, bool value)
{
  throw "Unsupported operation";
}

/*******************************************************************\

Function: satcheck_opensmt2t::is_in_conflict

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool satcheck_opensmt2t::is_in_conflict(literalt a) const
{
  throw "Unsupported operation";
}

/*******************************************************************\

Function: satcheck_opensmt2t::set_assumptions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void satcheck_opensmt2t::set_assumptions(const bvt &bv)
{
  throw "Unsupported operation";
}

/*******************************************************************\

Function: satcheck_opensmt2t::increase_id

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void satcheck_opensmt2t::increase_id()
{
  unsigned i = 0;

  while (i < id_str.length() && id_str[i] == 'Z') {
    id_str[i++] = 'A';
  }

  if (i < id_str.length()) {
    id_str[i]++;
  } else {
    id_str.append("A");
  }
}

/*******************************************************************\

Function: satcheck_opensmt2t::decode_id

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

unsigned satcheck_opensmt2t::decode_id(const char* id) const
{
  unsigned base = 1;
  unsigned i = 0;

  while (*id != 0) {
    i += base * (*id++ - 'A' + 1);
    base *= 'Z'-'A'+1;
  }
  return i-1;
}

/*******************************************************************\

Function: satcheck_opensmt2t::close_partition

  Inputs:

 Outputs:

 Purpose: Closes the interpolation partition by passing its CNF form
 (collected in current_partition) to the solver.

\*******************************************************************/

void satcheck_opensmt2t::close_partition()
{
  assert(current_partition != NULL);
  if (partition_count > 0){
    if (current_partition->size() > 1){
      top_level_formulas.push(logic->mkAnd(*current_partition));
    } else if (current_partition->size() == 1){
      std::cout << "Trivial partition (terms size = 1): " << partition_count << "\n";
      top_level_formulas.push((*current_partition)[0]);
    } else {
      std::cout << "Empty partition (terms size = 0): " << partition_count << "\n";
    }
  }
  current_partition = NULL;
}

