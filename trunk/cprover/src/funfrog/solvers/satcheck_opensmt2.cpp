/*******************************************************************\

Module: Wrapper for OpenSMT2. Based on satcheck_minisat.

Author: Grigory Fedyukovich

\*******************************************************************/

#include "satcheck_opensmt2.h"
#include "prop_itp.h"
#include <solvers/flattening/boolbv.h>

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
#ifdef PRODUCE_PROOF 
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
  unsigned base = 1;
  unsigned i = 0;

  while (*id != 0) {
    i += base * (*id++ - 'A' + 1);
    base *= 'Z'-'A'+1;
  }
  return i-1;
}

void satcheck_opensmt2t::insert_substituted(const itpt & itp, const std::vector<symbol_exprt> & symbols) {
    assert(!itp.is_trivial());
    const prop_itpt & prop_itp = dynamic_cast<const prop_itpt &>(itp);
    // FIXME: Dirty cast.
    boolbv_mapt& map = const_cast<boolbv_mapt &>((dynamic_cast<boolbvt*>(this->prop_convert.get())->get_map()));
    literalt* renaming = new literalt[prop_itp.get_no_variables()];

    // Fill the renaming table
    unsigned cannon_var_no = 1;
    for (const auto & symbol : symbols)
         {
        // Bool symbols are not in the boolbv_map and have to be treated separatelly
        if (symbol.type().id() == ID_bool) {
            literalt l = this->bool_expr_to_literal(symbol);
            assert(cannon_var_no < prop_itp.get_no_original_variables());
            renaming[cannon_var_no++] = l;
            continue;
        }
        bvt literals;
        const unsigned width = map.get_map_entry(symbol.get_identifier(), symbol.type()).width;
        literals.resize(width);
        map.get_literals(
                symbol.get_identifier(), symbol.type(), width, literals);
        for (unsigned i = 0; i < width; ++i) {
            literalt l = literals[i];
            assert(cannon_var_no < prop_itp.get_no_original_variables());
            renaming[cannon_var_no++] = l;
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
    if (sign)
        new_root_literal.invert();

    this->l_set_to_true(new_root_literal);

    delete [] renaming;
}

struct min_max_numbers{
    unsigned min;
    unsigned max;
};

min_max_numbers
compute_min_max_numbers_used(const boolbv_mapt::mappingt & mapping,
                                                 const std::vector<symbol_exprt> & symbols, prop_conv_solvert prop) {
    unsigned min_var = UINT_MAX;
    unsigned max_var = 0;
    // Get the bounds first
    for (const symbol_exprt & symbol : symbols ) {
        boolbv_mapt::mappingt::const_iterator pos = mapping.find(
                symbol.get_identifier());

        if (pos == mapping.end()) {
            // Bool symbols are not in the boolbv_map and have to be treated separately
            if (symbol.type().id() == ID_bool) {
                literalt l;
                if (!prop.literal(symbol, l)) {
                    unsigned var_no = l.var_no();
                    if (min_var > var_no) min_var = var_no;
                    if (max_var < var_no) max_var = var_no;
                }
            }
            continue;
        }
        const boolbv_mapt::map_entryt& entry = pos->second;

        // Check there are no issues with SSA translation that leaked here:
        // that it is always an SSA not an original symbol!
        assert(is_ssa_symbol(symbol));

        for (const auto & bit : entry.literal_map) {
            if (!bit.is_set)
                continue;

            unsigned var_no = bit.l.var_no();

            if (min_var > var_no) min_var = var_no;
            if (max_var < var_no) max_var = var_no;
        }
    }
    assert (min_var < UINT_MAX && max_var > 0);
    min_max_numbers res;
    res.min = min_var;
    res.max = max_var;
    return res;
}

void satcheck_opensmt2t::generalize_summary(prop_itpt & itp, const std::vector<symbol_exprt> & symbols) {
    itp.get_symbol_mask().clear();
    if (itp.is_trivial()) {
        return;
    }
    auto & prop = this->get_prop_conv_solver();
    // FIXME: Dirty cast.
    const boolbv_mapt::mappingt& mapping =
            dynamic_cast<const boolbvt&>(prop).get_map().mapping;
    auto min_max_var_no = compute_min_max_numbers_used(mapping, symbols, prop);

    auto min_var = min_max_var_no.min;
    auto max_var = min_max_var_no.max;

    assert(max_var > min_var);
    std::size_t var_count = (max_var - min_var) + 1;
    std::vector<unsigned> renaming(var_count, UINT_MAX);
    std::vector<unsigned> represented_symbol(var_count);

    // Fill the renaming table
    unsigned cannon_var_no = 1;
    unsigned current_symbol_idx = 0;
    // do not forget to increment current_symbol
    for (auto const & symbol : symbols) {
        auto pos = mapping.find(symbol.get_identifier());
        if (pos == mapping.end()) {
            // Bool symbols are not in the boolbv_map and have to be treated separatelly
            if (symbol.type().id() == ID_bool) {
                literalt l;
                if (!prop.literal(symbol, l)) {
                    // NOTE: We assume that the variables are unsigned and there are
                    // no duplicates. This migh not hold if some optimizations are added
                    // to the flattening process
                    assert (!l.sign());
                    // TODO: We need unique prop. variables only for the input parameters,
                    // if there is duplication among output variables (due to unification
                    // in symex), we just need to explicitly assert the unification by
                    // adding new clauses.
                    unsigned idx = l.var_no() - min_var;
                    assert (renaming[idx] == UINT_MAX);
                    renaming[idx] = cannon_var_no;
                    represented_symbol[idx] = current_symbol_idx;
                }
            }
//            else{
//                std::cout << "Symbol which is not boolean not found in bv mapping!\n";
//                std::cout << symbol.pretty() << '\n';
//                assert(false);
//            }
            ++current_symbol_idx;
            cannon_var_no++;
            continue;
        }
        const auto& entry = pos->second;

        for(auto const & bit : entry.literal_map)
        {
            if (!bit.is_set) {
                cannon_var_no++;
                continue;
            }

            // NOTE: We assume that the variables are unsigned and there are
            // no duplicates. This might not hold if some optimizations are added
            // to the flattening process
            unsigned idx = bit.l.var_no() - min_var;
            assert(idx >= 0);
            assert (renaming[idx] == UINT_MAX);
            renaming[idx] = cannon_var_no++;
            represented_symbol[idx] = current_symbol_idx;
        }
        ++current_symbol_idx;
    }

# ifdef DEBUG_ITP
    std::cout << "Renaming:" << std::endl;
  for (unsigned i = 0; i < max_var - min_var + 1; ++i) {
    if (i % 16 == 0) {
      if (i != 0) std::cout << std::endl;
    } else {
      std::cout << " ";
    }
    std::cout << (renaming[i] == UINT_MAX ? -1 : (int)renaming[i]);
  }
  std::cout << "Before generalization: " << std::endl;
  print(std::cout);
# endif

    // Do the renaming itself
    std::vector<bool> used_symbols;
    used_symbols.resize(symbols.size(), false);
    unsigned shift = itp.get_no_original_variables() - cannon_var_no;
    for (auto & clause : itp.get_clauses()) {
        for (auto & lit : clause) {
            // Only shift the artificial variables (present due to the Tseitin
            // encoding to CNF)
            if (lit.var_no() > max_var) {
                if (shift > lit.var_no()){
                    std::cout << "Failed to generalize interpolant\n";
                    // possibly, due to pointers
                    itp.set_root_literal(const_literal(true));
                    return;
                }
                lit.set(lit.var_no() - shift, lit.sign());
                continue;
            }

            int idx = lit.var_no() - min_var;
            // Sanity check, all variables used in the interpolant should be mapped.
            assert (idx >= 0 && "Failed to generalize interpolant; Index of represented_symbol is out of bound");
            assert(renaming[idx] != UINT_MAX);
            lit.set(renaming[idx], lit.sign());
            used_symbols[represented_symbol[idx]] = true;
        }
    }
    const literalt root_literal = itp.get_root_literal();
    if (root_literal.var_no() > max_var) {
        literalt new_root{root_literal.var_no() - shift, root_literal.sign()};
        itp.set_root_literal(new_root);
    } else {
        unsigned idx = root_literal.var_no() - min_var;
        // Sanity check, all variables used in the interpolant should be mapped.
        assert(renaming[idx] != UINT_MAX);
        literalt new_root{renaming[idx], root_literal.sign()};
        itp.set_root_literal(new_root);
        used_symbols[represented_symbol[idx]] = true;
    }

    // TODO: This line was broken - substitution could not guess variables, if some were not used
    // _no_variables -= shift;

//  std::cout << "_cannon_vars: " << cannon_var_no << std::endl;
//  std::cout << "_no_vars: " << _no_variables << std::endl;
//  std::cout << "_no_orig_vars: " << _no_orig_variables << std::endl;
    itp.set_no_variables(cannon_var_no + (itp.get_no_variables() - itp.get_no_original_variables()));
    itp.set_no_original_variables(cannon_var_no);

    auto & symbol_mask = itp.get_symbol_mask();
    symbol_mask.reserve(symbols.size());
    for (unsigned i = 0; i < symbols.size(); ++i) {
        symbol_mask.push_back(used_symbols[i]);
    }

    // TODO: Should we force mapping of common symbols to fresh prop. variables
    // in order to prevent unification?


}

