/*******************************************************************\

Module: Wrapper for OpenSMT2. Based on satcheck_minisat.

Author: Grigory Fedyukovich

\*******************************************************************/

#include "satcheck_opensmt2.h"
#include "prop_itp.h"
#include "naming_boolbv.h"

#ifdef DISABLE_OPTIMIZATIONS
#include <fstream>
#include <iostream>
#endif

satcheck_opensmt2t::satcheck_opensmt2t(const char * name, const namespacet & ns)
        : check_opensmt2t()
{
    initializeSolver(name);
    // TODO: move to separate method?
    auto bv_pointers = new naming_boolbv(ns, *this);
    bv_pointers->unbounded_array = bv_pointerst::unbounded_arrayt::U_AUTO;
    auto prop_conv_solver = std::unique_ptr<boolbvt>(bv_pointers);
    this->set_prop_conv_solvert(std::move(prop_conv_solver));
}

void satcheck_opensmt2t::initializeSolver(const char* name)
{
    osmt = new Opensmt(opensmt_logic::qf_bool, name);
    logic = &(osmt->getLogic());
    mainSolver = &(osmt->getMainSolver());
    const char* msg = nullptr;
    osmt->getConfig().setOption(SMTConfig::o_produce_inter, SMTOption(true), msg);
}

/*******************************************************************\

Function: satcheck_opensmt2t::convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

#ifdef PRODUCE_PROOF
void satcheck_opensmt2t::extract_itp(PTRef ptref,
  prop_itpt& target_itp) const
{
  ptref_cachet cache;
  target_itp.set_no_original_variables(_no_variables);
  target_itp.set_no_variables(_no_variables);
  target_itp.set_root_literal(extract_itp_rec(ptref, target_itp, cache));
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

/*******************************************************************\

Function: satcheck_opensmt2t::get_interpolant

  Inputs:

 Outputs:

 Purpose: Extracts the symmetric interpolant of the specified set of
 partitions. This method can be called only after solving the
 the formula with an UNSAT result.

\*******************************************************************/
void satcheck_opensmt2t::get_interpolant(const interpolation_taskt& partition_ids,
    interpolantst& interpolants) const
{
  assert(ready_to_interpolate);
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
//      std::cout << "Computed interpolant:\n" << logic->printTerm(itp_ptref) << '\n' << '\n';
      itpt* itp = new prop_itpt();
      extract_itp(itp_ptref, *(dynamic_cast <prop_itpt*> (itp)));
      interpolants.push_back(itp);
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

void satcheck_opensmt2t::generalize_summary(itpt * interpolant, std::vector<symbol_exprt> & common_symbols) {
    auto prop_itp = dynamic_cast<prop_itpt*>(interpolant);
    if(!prop_itp){
        throw std::logic_error{"SAT decider got non-propositional interpolant!"};
    }
    generalize_summary(*prop_itp, common_symbols);
}

void satcheck_opensmt2t::generalize_summary(prop_itpt & prop_itp, const std::vector<symbol_exprt> & symbols) {
    prop_itp.get_symbol_mask().clear();
    if (prop_itp.is_trivial()) {
        return;
    }
    auto & bv_converter = this->get_bv_converter();
    auto totalVars = prop_itp.get_no_variables();
    auto originalVars = prop_itp.get_no_original_variables();
    auto isTseitinVariable = [totalVars, originalVars](literalt lit){
        (void)totalVars; // for compilation warning in Release mode
        assert(lit.var_no() < totalVars);
        return lit.var_no() >= originalVars;
    };
    std::unordered_map<literalt::var_not, literalt::var_not> renaming;

    // Fill the renaming table
    unsigned cannon_var_no = 1;
//    unsigned current_symbol_idx = 0;
    // do not forget to increment current_symbol
    for (auto const & symbol : symbols) {
        auto const & bv = bv_converter.convert_bv(symbol);
        for(auto lit : bv){
//            MB: it can happen that some of the interface symbols were never converted, e.g. because of some optimizations
//            assert(lit.var_no() < originalVars);
            assert(!lit.sign()); // Can it be negated literal?
            renaming[lit.var_no()] = cannon_var_no++;
        }
    }
    const auto new_original_vars = cannon_var_no;
    const auto & const_renaming = renaming;
    // Do the renaming itself

    for (auto & clause : prop_itp.get_clauses()) {
        for (auto & lit : clause) {
            if(const_renaming.find(lit.var_no()) != const_renaming.end()) // literal from interface symbol
            {
                lit.set(const_renaming.at(lit.var_no()), lit.sign());
            }
            else // literal NOT from interface symbol, should be literal corresponding to Tseitin encoding
            {
                if(!isTseitinVariable(lit)){ // it is not Tseiting variable
                    // this can happen e.g. when function works with pointers
                    // this interpolant cannot be generalized in meaningful way
//                    warning() << "Propositional interpolant contained variables it should not caontain\n" << eom;
                    prop_itp.set_trivial();
                    return;
                }
                else // it is Tseitin variable
                {
                    assert(lit.var_no() < prop_itp.get_no_variables());
                    literalt renamed{cannon_var_no++, lit.sign()};
                    renaming[lit.var_no()] = renamed.var_no();
                    lit = renamed;
                }
            }
        }
    }

    const literalt root_literal = prop_itp.get_root_literal();
    const auto root_literal_var = root_literal.var_no();
    if(const_renaming.find(root_literal_var) != const_renaming.end()){
        prop_itp.set_root_literal(literalt{const_renaming.at(root_literal_var), root_literal.sign()});
    }
    else{
        assert(false);
        throw std::logic_error{"Root literal of propositional interpolant is unknown variable!"};
    }

//  std::cout << "_cannon_vars: " << cannon_var_no << std::endl;
//  std::cout << "_no_vars: " << _no_variables << std::endl;
//  std::cout << "_no_orig_vars: " << _no_orig_variables << std::endl;
    prop_itp.set_no_variables(cannon_var_no);
    prop_itp.set_no_original_variables(new_original_vars);

    // TODO: we should probaly not consider used symbols at all
    auto & symbol_mask = prop_itp.get_symbol_mask();
    symbol_mask.reserve(symbols.size());
    for (unsigned i = 0; i < symbols.size(); ++i) {
        symbol_mask.push_back(true);
    }
}

#endif // PRODUCE_PROOF

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
//    ptrefs.reserve(_no_variables);
//    while (ptrefs.size() < _no_variables) {
//        increase_id();
//        const char* vid = id_str.c_str();
//        ptrefs.push_back(logic->mkBoolVar(vid));
//    }

  ptrefs.reserve(_no_variables);

  while (ptrefs.size() < _no_variables) {
      if(ptrefs.size() >= lits_names.size() || ptrefs.empty() || lits_names[ptrefs.size()].empty()){
          increase_id();
          set_variable_name(literalt{static_cast<unsigned>(ptrefs.size()), false}, id_str);
      }
      //assert(!lits_names[ptrefs.size()].empty());
      if(lits_names[ptrefs.size()].empty()){
         for(auto & name : lits_names){
             std::cout << name << '\n';
         }
         assert(false);
      }
      ptrefs.push_back(logic->mkBoolVar(lits_names[ptrefs.size()].c_str()));
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
    current_partition.push_back(tmp);
    return;
  }
//
  add_variables();
  vec<PTRef> or_args;
  convert(new_bv, or_args);

  current_partition.push_back(logic->mkOr(or_args));
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
      out_sat_pre_query.open(pre_queries_file_name+"_"+std::to_string(get_unique_index())+".smt2");
      
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
  
  if (!last_partition_closed) {
    close_partition();
  }

  insert_top_level_formulas();

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
    std::string name{id};
    auto it = std::find(lits_names.begin(), lits_names.end(), name);
    assert(it != lits_names.end());
    return it - lits_names.begin();
//  unsigned base = 1;
//  unsigned i = 0;
//
//  while (*id != 0) {
//    i += base * (*id++ - 'A' + 1);
//    base *= 'Z'-'A'+1;
//  }
//  return i-1;
}

void satcheck_opensmt2t::insert_substituted(const itpt & itp, const std::vector<symbol_exprt> & symbols) {
    assert(!itp.is_trivial());
    const prop_itpt & prop_itp = dynamic_cast<const prop_itpt &>(itp);
    auto & bv_converter = this->get_bv_converter();
    std::vector<literalt> renaming {prop_itp.get_no_variables(), literalt{}};

    // Fill the renaming table
    unsigned cannon_var_no = 1;
    for (const auto & symbol : symbols) {
        auto const & bv = bv_converter.convert_bv(symbol);
        for (auto lit : bv) {
            renaming[cannon_var_no++] = lit;
        }
    }
    // Allocate new variables for the auxiliary ones (present due to the Tseitin
    // encoding to CNF)
    for (unsigned i = prop_itp.get_no_original_variables(); i < prop_itp.get_no_variables(); ++i) {
        renaming[i] = this->new_variable();
    }

    // Rename and output the clauses
    bvt tmp_clause;
    for (const auto & clause : prop_itp.get_clauses())
        {
        tmp_clause = clause;

        for (auto & lit : tmp_clause) {
            // Rename
            bool sign = lit.sign();
            lit = renaming[lit.var_no()];
            assert(literalt::unused_var_no() != lit.var_no());
            if (sign){
                lit.invert();
            }
        }
        // Assert the clause
        this->lcnf(tmp_clause);
    }

    const literalt root_literal = prop_itp.get_root_literal();
    // Handle the root
    bool sign = root_literal.sign();
    literalt new_root_literal = renaming[root_literal.var_no()];
    assert(literalt::unused_var_no() != new_root_literal.var_no());
    if (sign)
        new_root_literal.invert();

    this->l_set_to_true(new_root_literal);
}

void satcheck_opensmt2t::set_variable_name(literalt a, const std::string & name) {
    while(lits_names.size() <= a.var_no()){
        lits_names.emplace_back("");
    }
    assert(lits_names[a.var_no()].empty());
    assert(!name.empty());
    lits_names[a.var_no()] = name;
}

literalt satcheck_opensmt2t::new_variable() {
    return cnft::new_variable();
}

bool satcheck_opensmt2t::is_overapprox_encoding() const {
    return false;
}

