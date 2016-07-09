/*******************************************************************\

Module: Wrapper for OpenSMT2. Based on satcheck_minisat.

Author: Grigory Fedyukovich

\*******************************************************************/

#include "satcheck_opensmt2.h"

void satcheck_opensmt2t::initializeSolver()
{
  osmt = new Opensmt(opensmt_logic::qf_bool);
  logic = &(osmt->getLogic());
  mainSolver = &(osmt->getMainSolver());
  const char* msg;
  osmt->getConfig().setOption(SMTConfig::o_produce_inter, SMTOption(true), msg);
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
  literalt result;

  if (cached_it != ptref_cache.end()) {
    return cached_it->second;
  }

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
      Pterm& ptm = logic->getPterm(ptref);
      assert(ptm.size() == 0);
      result.set(decode_id(logic->getSymName(ptref)), false);
  } 
    
  ptref_cache.insert(ptref_cachet::value_type(ptref, result));
  return result;
}

// helper interpolation method taken from opensmt
void satcheck_opensmt2t::produceConfigMatrixInterpolants (const vector< vector<int> > &configs, vector<PTRef> &interpolants)
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
void satcheck_opensmt2t::get_interpolant(const interpolation_taskt& partition_ids,
    interpolantst& interpolants)
{
  assert(ready_to_interpolate);

  // Set labeling function
  const char* msg;
  osmt->getConfig().setOption(SMTConfig::o_itp_bool_alg, SMTOption(itp_algorithm), msg);

  SimpSMTSolver& solver = osmt->getSolver();

  // Create the proof graph
  solver.createProofGraph();

  vector<PTRef> itp_ptrefs;

  // iterative call of getSingleInterpolant:
  produceConfigMatrixInterpolants(partition_ids, itp_ptrefs);

  solver.deleteProofGraph();

  for(unsigned i = 0; i < itp_ptrefs.size(); ++i)
  {
      prop_itpt itp;
      extract_itp(itp_ptrefs[i], itp);
      interpolants.push_back(prop_itpt());
      interpolants.back().swap(itp);
  }
}



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

/*******************************************************************\

Function: satcheck_opensmt2t::l_get

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

tvt satcheck_opensmt2t::l_get(literalt a) const
{
  if (a.is_true())
    return tvt(true);
  else if (a.is_false())
    return tvt(false);

  tvt tvtresult(tvt::TV_UNKNOWN);
  ValPair a_p = mainSolver->getValue(ptrefs[a.var_no()]);
  lbool lresult = (*a_p.val == *true_str) ? l_True : l_False;

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
    PTRef tmp = logic->mkConst(logic->getSort_bool(), Logic::tk_false);
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

  if (dump_queries){
    char* msg1;
    mainSolver->writeSolverState_smtlib2("__SAT_query", &msg1);
  }

  assert(status != ERROR);
  ready_to_interpolate = false;

  if (current_partition != NULL) {
    close_partition();
  }

  add_variables();

  sstat r = mainSolver->check();

  if (r == s_True) {
    status = SAT;
    return P_SATISFIABLE;
  } else if (r == s_False) {
    ready_to_interpolate = true;
  } else {
    throw "Unexpected OpenSMT result.";
  }

  status = UNSAT;
  return P_UNSATISFIABLE;
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
  char *msg;
  if (partition_count > 0){
    if (current_partition->size() > 1){
      mainSolver->insertFormula(logic->mkAnd(*current_partition), &msg);
    } else if (current_partition->size() == 1){
      std::cout << "Trivial partition (terms size = 1): " << partition_count << "\n";
      mainSolver->insertFormula((*current_partition)[0], &msg);
    } else {
      std::cout << "Empty partition (terms size = 0): " << partition_count << "\n";
    }
  }
  current_partition = NULL;
}

