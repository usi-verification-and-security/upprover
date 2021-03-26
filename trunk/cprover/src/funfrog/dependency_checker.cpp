#include "dependency_checker.h"

#include <memory>
#include <fstream>
#include <util/expr_util.h>

#ifdef DISABLE_OPTIMIZATIONS
#include "expr_pretty_print.h"
#include <iostream>
#endif

#include "nopartition/hifrog_symex_target_equation_no_partition.h"
#include "subst_scenario.h"
#include "partitioning_target_equation.h"
#include "solvers/satcheck_opensmt2.h"
#include "utils/naming_helpers.h"
#include "conversion_utils.h"
#include <funfrog/solvers/solver_options.h>

#include <sstream>
#include <map>
#include <funfrog/utils/time_utils.h>
#include <langapi/language_util.h>

#define VERBOSE false
using namespace hifrog;

/*******************************************************************\
 
 Note: This method gets triggered when "claims-opt" or "claims-order" is ON.

 Purpose:

\*******************************************************************/
void dependency_checkert::do_it(partitioning_target_equationt &equation){

  reconstruct_exec_SSA_order(equation); // the only place where partition_target_equation is used.

  auto initial=timestamp();

  std::ofstream hl_list;
  hl_list.open ("__hl_list");
  std::size_t idx = 0; // index to ssa_steps
    for(auto step : SSA_steps)
    {
      if (step.is_assert() && !omega.is_assertion_in_loop(step.source.pc)){
        asserts.push_back(idx);
        //cout << "ID: " << it->source.pc->location.get_claim() << " Condition: " << from_expr(ns, "", it->cond_expr) << '\n';
//        instances[step->source.pc->source_location.get_property_id().c_str()]++;
        hl_list << "Assertion: " << step.source.pc->source_location.get_property_id().c_str() << '\n';
      }
      ++idx;
    }

    hl_list.close();

//    cout << "SSA Assertions: " << asserts.size();
//    cout << '\n';

    auto temp_end = timestamp();
    auto duration = time_gap(temp_end,initial);
    //std::cout << "TIME FOR find_var_deps (should ~ be zero): " << (duration) << '\n';

    initial=timestamp();

    // TODO: this takes a lot of time. Oct.2014: optimized a little bit
    find_assert_deps();   //2

    temp_end = timestamp();
    duration = time_gap(temp_end,initial);
    status () << "TIME FOR find_assert_deps: " << (duration) << eom;

    initial = timestamp();

    //TODO: FIX THIS!
    find_implications();   //3

    temp_end = timestamp();
    duration = time_gap(temp_end,initial);

    status() << "TIME FOR ASSERTION OPTIMIZATIONS: " << (duration) << eom;

  //TODO: make a proper cmd-parameter
  std::ifstream just_dep;
  just_dep.open ("__just_hl_dep");
  if (just_dep.good()) {
      status () << "__just_hl_dep file is in the current directory. Exiting..." << eom;
      just_dep.close();
      exit(1);
  }
  just_dep.close();

//  get_minimals();

//  initial = timestamp();
//  std::cout << "TIME FOR get_minimals: " << (initial - final) << '\n';
}

// For no partition version
void dependency_checkert::do_it(hifrog_symex_target_equationt &equation){

    //reconstruct_exec_SSA_order(equation); // the only place where partition_target_equation is used.
    for(auto it=equation.SSA_steps.begin();
      it!=equation.SSA_steps.end();
      it++)
    {
      symex_target_equationt::SSA_stept& SSA_step=(*it);
      this->SSA_steps.push_back(SSA_step);
      SSA_map[SSA_step.ssa_full_lhs] = SSA_step.cond_expr;
    }

    auto initial=timestamp();

    std::ofstream hl_list;
    hl_list.open ("__hl_list");
    std::size_t idx = 0;
    for(auto step : SSA_steps)
    {
      if (step.is_assert() && !omega.is_assertion_in_loop(step.source.pc)){
        asserts.push_back(idx);
        //cout << "ID: " << it->source.pc->location.get_claim() << " Condition: " << from_expr(ns, "", it->cond_expr) << '\n';
//        instances[step->source.pc->source_location.get_property_id().c_str()]++;
        hl_list << "Assertion: " << step.source.pc->source_location.get_property_id().c_str() << '\n';
      }
      ++idx;
    }

    hl_list.close();

//    cout << "SSA Assertions: " << asserts.size();
//    cout << '\n';

    //auto temp_end = timestamp();
    //auto duration = time_gap(temp_end , initial);
    //std::cout << "TIME FOR find_var_deps (should ~ be zero): " << (duration) << '\n';

    initial=timestamp();

    // TODO: this takes a lot of time. Oct.2014: optimized a little bit
    find_assert_deps();

    auto temp_end = timestamp();
    auto duration = time_gap(temp_end , initial);
    status () << "TIME FOR find_assert_deps: " << (duration) << eom;

    initial = timestamp();

    //TODO: FIX THIS!
    find_implications();

    temp_end = timestamp();
    duration = time_gap(temp_end , initial);

    status () << "TIME FOR ASSERTION OPTIMIZATIONS: " << (duration) << eom;

    //TODO: make a proper cmd-parameter
    std::ifstream just_dep;
    just_dep.open ("__just_hl_dep");
    if (just_dep.good()) {status () << "__just_hl_dep file is in the current directory. Exiting... " << eom; just_dep.close(); exit(1);}
    just_dep.close();
}
/*******************************************************************\
 
 Function: call 1

 Purpose:

\*******************************************************************/
void dependency_checkert::find_var_deps(UnionFind<std::string> &deps_ds, std::map<std::string, bool> &visited)
{

    // ============ DISJOINT SETS EDITING BEGINS

    auto it = SSA_steps.begin() + asserts.front();
    auto end = SSA_steps.begin() + asserts.back();
    for( ; it != end; ++it)
    {
        auto ass = *it;
      if (ass.is_assignment() || ass.is_assume() || ass.is_assert())
      {
            symbol_sett all_symbols;
            symbol_sett guard_symbols;

            get_expr_symbols(ass.cond_expr, all_symbols);
            get_expr_symbols(SSA_map[ass.cond_expr], all_symbols);

//            for (symbol_sett::iterator sym_it = all_symbols.begin(); sym_it != all_symbols.end(); ++sym_it){
//              if (as_string(*sym_it).find("\\guard") < 10000){ //dirty hack
//                 //cout <<"guard symbol: " << as_string(*sym_it)  << "\n";
//                  // all_symbols.erase(sym_it);
//                //get_expr_symbols(SSA_map[(*it)->cond_expr], all_symbols);
//              }
//            }
            if (!all_symbols.empty())
            {
              std::string first_sym = as_string(*(all_symbols.begin()));
            	if (!visited[first_sym])
                {
                  deps_ds.makeSet(first_sym);
//                  equation_symbols.push_back(first_sym);
                  visited[first_sym] = true;
//                  cout << "I have visited a variable: " << first_sym << " ["
//                      << (visited[first_sym]?"true":"false") << "]" << '\n';
                }
            }

//            else
//            {
//            	cerr << "Empty list of symbols has been found. The corresponding instruction is printed below." << '\n';
//            	cerr << "Instruction type: ";
//            	if ((*it)->is_assume()) cerr << "Assumption.";
//            	else if ((*it)->is_assignment()) cerr << "Assignment.";
//            	else cerr << "Neither assertion nor assignment.";
//            	cerr << '\n';
//            	cerr << "Guard: " << from_expr(ns, "", (*it)->guard) << '\n';
//            	cerr << "Condition: " << from_expr(ns, "", (*it)->cond_expr) << '\n';
//            	cerr << "High level code line number: " << (*it)->source.pc->location.as_string() << '\n';
//            }

            for (symbol_sett::iterator sym_it = all_symbols.begin(); sym_it != all_symbols.end(); ++sym_it)
            {
              std::string next_sym = as_string(*sym_it);
            	if (!visited[next_sym])
              {
//                equation_symbols.push_back(next_sym);
                deps_ds.makeSet(next_sym);
                visited[next_sym] = true;
//                cout << "I have visited a variable: " << next_sym << " ["
//                    << (visited[next_sym]?"true":"false") << "]" << '\n';
              }
            	//cout << "Merging: " << as_string(*(all_symbols.begin())) << " and " <<  next_sym <<"\n";
              deps_ds.merge(as_string(*(all_symbols.begin())), next_sym);
            	//string x = deps_ds->find_set(as_string(*sym_it));
            	//cout << "Printing test of variable: " << x << '\n';
            	//exit(1);
            }
        }
    }

    //FIXME: Determine if compression is needed for greater efficiency
    //deps_ds.compress_sets(equation_symbols.begin(), equation_symbols.end());

//    cout << "Number of disjoint variable sets: " << (int)deps_ds.count_sets(equation_symbols.begin(), equation_symbols.end()) << '\n';

}
/*******************************************************************\
 
 Function: call 2

 Purpose:

\*******************************************************************/
void dependency_checkert::find_assert_deps()
{
    int deps=0;
    int indeps=0;
    bool doubleforbreak;
    std::map<std::string, bool> visited;
    UnionFind<std::string> uf;

    find_var_deps(uf, visited);

    for (unsigned i = 0; i < asserts.size(); i++)
    {
      auto assert1_idx = asserts[i];
      auto & assert_1 = SSA_steps[assert1_idx];
      symbol_sett first_symbols;
      get_expr_symbols(assert_1.guard, first_symbols);
      get_expr_symbols(assert_1.cond_expr, first_symbols);

      for (unsigned j = i + 1; j < asserts.size(); j++)
      {
        indeps++;
        auto assert2_idx = asserts[j];
        auto & assert_2 = SSA_steps[assert2_idx];
        if (!compare_assertions(assert1_idx, assert2_idx))
          continue;

        symbol_sett second_symbols;
        get_expr_symbols(assert_2.guard, second_symbols);
        get_expr_symbols(assert_2.cond_expr, second_symbols);
        doubleforbreak = false;
        for (auto first_symit = first_symbols.begin();
            (first_symit != first_symbols.end() && (!doubleforbreak));
            ++first_symit)
          {
        	for (auto second_symit = second_symbols.begin();
        	    (second_symit != second_symbols.end() && (!doubleforbreak));
        	    ++second_symit)
            {
        	    if (visited[as_string(*first_symit)] && visited[as_string(*second_symit)])
                if (uf.find(as_string(*first_symit)) == uf.find(as_string(*second_symit)) )
                {
                  assert_deps[assert1_idx][assert2_idx] = true;
                  doubleforbreak = true;
                  deps++;
//                  cout << "The following assertions are dependent!" << '\n';
//                  cout << from_expr(ns, "", (*assert_1)->cond_expr) << '\n';
//                  cout << from_expr(ns, "", (*assert_2)->cond_expr) << '\n';
                }
            }
          }
        }
    }

//    cout << "Syntactic independencies found: " << (indeps - deps) << '\n';
//    cout << "Syntactic dependencies found: " << deps << '\n';

}

//static bool compare_asserts(dependency_checkert::SSA_step_reft a, dependency_checkert::SSA_step_reft b)
//{
//	return (distance(a, b) < 0);
//}
/*******************************************************************\
 
 Function:

 Purpose:

\*******************************************************************/
bool dependency_checkert::compare_assertions(std::size_t idx1, std::size_t idx2){
    assert(idx2 > idx1);
    return (idx2 - idx1) < treshold;
}

#ifdef DISABLE_OPTIMIZATIONS
void dependency_checkert::print_SSA_steps_infos()
{
//TODO: integrate with new CProver
/*  map<string,map<string,bool> > var_deps;

  //printf("Sono dentro la dependency analysis!\n");
  std::cout << '\n' << "Printing SSA data" << '\n' << '\n';
    for(SSA_stepst::iterator it = SSA_steps.begin(); it!=SSA_steps.end(); ++it)
    {
      it->output(ns, std::cout);
      std::cout << "Andrea's data:\n";
      std::cout << "Guard = " << from_expr(ns, "", it->guard) << '\n';
      if (it->is_assignment())
      {
            std::cout << "  Type = ASSIGNMENT" << '\n';
            std::cout << "  Assignment type = ";
            if (it->assignment_type == symex_targett::HIDDEN) std::cout << "HIDDEN" << '\n';
            else if (it->assignment_type == symex_targett::STATE) std::cout << "STATE" << '\n';
            else std::cout << "NOT EXPECTED" << '\n';
            std::cout << "  Condition expression = " << from_expr(ns, "", it->cond_expr) << '\n';
            std::cout << "Symbols in the expression: ";
            print_expr_symbols(std::cout, it->cond_expr);
            std::cout << '\n';
            std::cout << "left-hand side: " << from_expr(ns, "", it->ssa_lhs) << '\n';
            std::cout << "Symbols in the left-hand side: ";
            print_expr_symbols(std::cout, it->ssa_lhs);
            std::cout << '\n';
            std::cout << "right-hand side: " << from_expr(ns, "", it->ssa_rhs) << '\n';
            std::cout << "Symbols in the right-hand side: ";
            print_expr_symbols(std::cout, it->ssa_rhs);
            std::cout << '\n';
            symbol_sett lhs_symbols, rhs_symbols, guard_symbols;
            get_expr_symbols(it->ssa_lhs, lhs_symbols);
            get_expr_symbols(it->ssa_rhs, rhs_symbols);
            get_expr_symbols(it->guard, guard_symbols);
            dstring temp;
            for (symbol_sett::iterator lhs_it = lhs_symbols.begin(); lhs_it != lhs_symbols.end(); ++lhs_it)
            {
              string lid = as_string(*lhs_it);
                for (symbol_sett::iterator rhs_it = rhs_symbols.begin(); rhs_it != rhs_symbols.end(); ++rhs_it)
                {
                  string rid = as_string(*rhs_it);
                  std::cout << "Dependency " << variable_name(*lhs_it) << " <- " << variable_name(*rhs_it) << " is being added." << '\n';
                  var_deps[lid][rid] = DEPT;
                }
                for (symbol_sett::iterator guard_it = guard_symbols.begin(); guard_it != guard_symbols.end(); ++guard_it)
                {
                  string gid = as_string(*guard_it);
                  std::cout << "Dependency " << variable_name(*lhs_it) << " <- " << variable_name(*guard_it) << " is being added." << '\n';
                  var_deps[lid][gid] = DEPT;
                }
            }
        }
      else if (it->is_assert())
      {
        std::cout << "  Type = ASSERT" << '\n';
        std::cout << "  Condition expression = " << from_expr(ns, "", it->cond_expr) << '\n';
        std::cout << "  Comment = " << it->comment << '\n';
      }
      else if (it->is_assume())
      {
        std::cout << "  Type = ASSUME" << '\n';
        std::cout << "  Condition expression = " << from_expr(ns, "", it->cond_expr) << '\n';
      }
      else if (it->is_location())
      {
        std::cout << "  Type = LOCATION" << '\n';
      }
      else if (it->is_output())
      {
        std::cout << "  Type = OUTPUT" << '\n';
      }
      else
      {
        std::cout << "  Type = NOT EXPECTED" << '\n';
      }
        if(it->source.is_set)
        {
          std::cout << "  Thread = " << it->source.thread_nr << '\n';
          if(it->source.pc->location.is_not_nil())
            std::cout << "  Location = " << it->source.pc->location << '\n';
          else
            std::cout << '\n';
        }
        if (it->cond_expr.has_operands())
        {
            std::cout << "  Operands:" << '\n';

            int k = 0;
            Forall_operands(op, it->cond_expr)
            {
            std::cout << "    Op[" << k << "] = ";
            //expr_pretty_print(tempstr, *op, 2);
            print_expr_operands(std::cout, *op, 2);
            k++;
            }

        }
        std::cout << '\n';
    }
    std::cout << "Printing dependencies:" << '\n';
    map<string,map<string,bool> >::iterator dep_it;
    for ( dep_it=var_deps.begin() ; dep_it != var_deps.end(); dep_it++ )
    {
      std::cout << variable_name((*dep_it).first) << " <- ";
      print_dependents((*dep_it).second, std::cout);
      std::cout << '\n';
    }
    */
}
#endif
/*******************************************************************\
 
 Function:

 Purpose:

\*******************************************************************/
void dependency_checkert::print_dependents(std::map<std::string,bool> dependents, std::ostream &out)
{
  std::map<std::string,bool>::iterator it;
  int count = 0;
  for ( it=dependents.begin() ; it != dependents.end(); it++ )
  {
    if ((*it).second == true) {if (count > 0) out << ", "; out << variable_name((*it).first); count++;}
  }
}
/*******************************************************************\
 
 Function:

 Purpose:

\*******************************************************************/
std::string dependency_checkert::variable_name(dstringt name)
{
  return variable_name(as_string(name));
}

std::string dependency_checkert::variable_name(std::string name)
{
  return name.substr(name.find_last_of(':') + 1, 10);
}
/*******************************************************************\
 
 Function:

 Purpose:

\*******************************************************************/
void dependency_checkert::get_expr_symbols(const exprt &expr, symbol_sett& symbols)
{

  forall_operands(it, expr)
    get_expr_symbols(*it, symbols);

  if(expr.id()==ID_symbol)
  {
    const irep_idt& id = to_symbol_expr(expr).get_identifier();
    symbols.insert(id);
  }
}
/*******************************************************************\
 
 Function:

 Purpose:

\*******************************************************************/
void dependency_checkert::print_expr_symbols(std::ostream &out, exprt expr)
{
    symbol_sett s;
    get_expr_symbols(expr, s);
    print_expr_symbols(out, s);
}

void dependency_checkert::print_expr_symbols(std::ostream &out, symbol_sett& s)
{
    for (auto const & symbol : s)
    {
      out << variable_name(symbol) << " ";
    }
    //s.clear();
}
/*******************************************************************\
 
 Function:

 Purpose:

\*******************************************************************/
#ifdef DISABLE_OPTIMIZATIONS
void dependency_checkert::print_expr_operands(std::ostream &out, exprt expr, int indent)
{
  if (expr.has_operands())
  {
    expr_pretty_printt pretty(out);
    pretty(expr);
  }
  else out << from_expr(ns, "", expr) << '\n';
  if (expr.has_operands())
  {
    int k = 0;
        Forall_operands(op, expr)
        {
          for (int i=0; i<indent; i++) out << " ";
          out << "    Op[" << k << "] = ";
          print_expr_operands(out, *op, indent + 2);
          k++;
          }
  }
}

void dependency_checkert::print_SSA_steps()
{
//    for(symex_target_equationt::SSA_stepst::iterator it = SSA_steps.begin(); it!=SSA_steps.end(); ++it)
//    {
    for (const auto & ssa_stp : SSA_steps) {
      ssa_stp.output(std::cout);
    }
}
#endif
/*******************************************************************\
 
 Function:

 Purpose:

\*******************************************************************/
// TODO: send equation as in parameter - requires no additional changes!
void dependency_checkert::reconstruct_exec_SSA_order(partitioning_target_equationt &equation){
  const SSA_steps_orderingt& SSA_steps = equation.get_steps_exec_order();
  for(auto ssa_step : SSA_steps)
  {
    symex_target_equationt::SSA_stept& SSA_step = *ssa_step;
    this->SSA_steps.push_back(SSA_step);
    SSA_map[SSA_step.ssa_full_lhs] = SSA_step.cond_expr;
  }
}
/*******************************************************************\
 
 Function: call 3

 Purpose:

\*******************************************************************/
long dependency_checkert::find_implications() {
    long true_time, false_time, to_time;
    true_time = 0;
    false_time = 0;
    to_time = 0;
    //bool mustprint = false;
    unsigned notdisc = 0;
    unsigned discarded = 0;
    int checks=0;
    int impchecks=0;
    std::vector<bool> stronger(asserts.size(), false);
    std::vector<bool> weaker(asserts.size(), false);

    std::ofstream hl_may_impl;
    hl_may_impl.open ("__hl_may_impl");

    for (unsigned i = 0; i < asserts.size(); i++)
    {
        auto assert1_idx = asserts[i];
        auto assert_1 = SSA_steps[assert1_idx];
        for (unsigned j = i+1; j < asserts.size(); j++)
        {
            checks++;
            std::pair<bool, timet> checkres;
            auto assert2_idx = asserts[j];
            auto assert_2 = SSA_steps[assert2_idx];
            if (compare_assertions(assert1_idx, assert2_idx)
                && assert_deps[assert1_idx][assert2_idx] == DEPT
                    )
            {
                impchecks++;
                if (VERBOSE)
                {
                    status() << "Comparing the assertions " <<
                             from_expr(ns, "", assert_1.cond_expr) << " and " <<
                             from_expr(ns, "", assert_2.cond_expr) << eom;
                }
                checkres = check_implication(SSA_steps.begin() + assert1_idx, SSA_steps.begin() + assert2_idx);

                if (checkres.first == true)
                {
                    true_time = true_time +  checkres.second.count() ;
                    if (VERBOSE) {status() << "check_implication returned TRUE" << eom;}
                    if ( checkres.second.count() <= impl_timeout)
                    {
                        assert_imps[assert1_idx][assert2_idx] = IMP;
                        if (VERBOSE)
                        {
                            status() << "Adding the assertion implication \n (" <<
                                     from_expr(ns, "", assert_1.cond_expr) << ") [" << assert_1.source.pc->source_location.get_line() << "] [stronger] \n => \n (" <<
                                     from_expr(ns, "", assert_2.cond_expr) << ") [" << assert_2.source.pc->source_location.get_line() << "] [weaker]" << eom;
                        }

                        weaker[i] = false;
                        stronger[j] = false;
                        hl_may_impl << assert_1.source.pc->source_location.get_property_id() << " " <<
                                    assert_2.source.pc->source_location.get_property_id() << " " <<
                                    assert1_idx << " " <<
                                    assert2_idx << std::endl;

                        discarded++;
                    }
                    else
                    {
                        notdisc++;
                    }
                }
                else
                {
                    false_time = false_time +  checkres.second.count() ;
                    if (VERBOSE) { status () << "check_implication returned FALSE" << eom;}
                }
                if ( checkres.second.count()  > impl_timeout)
                {
                    long exceeding = time_gap( checkres.second.count(),impl_timeout);
                    warning () << "Timeout " << (impl_timeout/1000) << "." <<
                               (impl_timeout%1000)/10 << " exceeded of " <<
                               (exceeding/1000) << "." <<
                               (exceeding%1000)/10 << " seconds." << eom;
                    to_time = to_time + exceeding;
                }
            }
        }
    }

//    std::cout << "Printing assertion implications:" << std::endl;
//    for (map<SSA_steps_it,map<SSA_steps_it,bool> >::iterator dep_first_it = assert_imps.begin(); dep_first_it != assert_imps.end(); ++dep_first_it)
//      for (map<SSA_steps_it,bool>::iterator dep_second_it = dep_first_it->second.begin(); dep_second_it != dep_first_it->second.end(); ++dep_second_it)
//      std::cout << "(" << from_expr(ns, "", dep_first_it->first->cond_expr) << " => " << from_expr(ns, "", dep_second_it->first->cond_expr) << ")" << std::endl;

    hl_may_impl.close();

    status () << "Discarded assertions: " << discarded << eom;
    if (notdisc > 0) warning () << "WARNING: " << notdisc << " true implications exceeded timeout!" << eom;

    status () << "Total number of implication checks: " << impchecks << eom;
    status () << "Total number of comparisons: " << checks << eom;

    for (int i = asserts.size() - 1; i >= 0; i--)
    {
        if (weaker[i] == true)
        {
            auto removable = SSA_steps[asserts[i]];
            status () << "Removing << " << removable.source.pc->source_location.get_line() << eom;
            removable.ignore = true;
        }
    }
    try{
        std::ofstream hl_stronger;
        std::ofstream hl_weaker;
        hl_stronger.open ("__hl_stronger");
        hl_weaker.open ("__hl_weaker");
        //int hldiscardable = 0;
        for (int i = asserts.size() - 1; i >= 0; i--){
            auto ass = SSA_steps[asserts[i]];
            if (weaker[i] == true)
                hl_weaker << ass.source.pc->source_location.get_property_id().c_str() << std::endl;
            if (stronger[i] == true)
                hl_stronger << ass.source.pc->source_location.get_property_id().c_str() << std::endl;
        }

        hl_stronger.close();
        hl_weaker.close();
    }  catch (const std::bad_alloc &e)
    {
        error()  << "smth is very wrong: " << e.what()  << eom;

    }
    return to_time;
}

void dependency_checkert::convert_assumptions(
        convertort &convertor, SSA_steps_it &it1, SSA_steps_it &it2)
{
    SSA_steps_it it=it1;
    while(it!=it2)
    {
        if(((*it).is_assume() || ((*it).is_assert() && it != it2)) && !(*it).ignore)
        {
            //std::cout << "convert assume :" << from_expr(ns, "", (*it)->cond_expr) <<"\n";
            convertor.set_to_true((*it).cond_expr);
            set_guards_to_true(convertor, ((*it).cond_expr));
        }
        it++;
    }
}
/*******************************************************************\
 
 Function:

 Purpose:

\*******************************************************************/
void dependency_checkert::convert_assertions(
        convertort &convertor, SSA_steps_it &it2)
{
    assert((*it2).is_assert());
    //std::cout << "convert assert :" << from_expr(ns, "", (*it2)->cond_expr) <<"\n";
    set_guards_to_true(convertor, ((*it2).cond_expr));
    convertor.set_to_false((*it2).cond_expr);
}

void dependency_checkert::convert_io(
        convertort &convertor, SSA_steps_it &it1, SSA_steps_it &it2)
{
    unsigned io_count=0;
    SSA_steps_it it=it1;
    SSA_steps_it it3=it2;
    it3++;

    while (it!=it3){
        for(std::list<exprt>::const_iterator
                    o_it=(*it).io_args.begin();
            o_it!=(*it).io_args.end();
            o_it++)
        {
            exprt tmp=*o_it;
            if(tmp.is_constant() ||
               tmp.id()==ID_string_constant)
                (*it).converted_io_args.push_back(tmp);
            else
            {
                symbol_exprt symbol;
                symbol.type()=tmp.type();
                symbol.set_identifier(CProverStringConstants::IO_CONST + std::to_string(io_count++));
                convertor.set_to_true(equal_exprt(tmp, symbol));
                (*it).converted_io_args.push_back(symbol);
            }
        }
        it++;
    }
}
/*******************************************************************\
 
 Function:

 Purpose:

\*******************************************************************/
void dependency_checkert::set_guards_to_true(convertort &convertor, const exprt &exp){
    if (exp.has_operands())
    {
        for (unsigned i = 0; i < exp.operands().size(); i++){
            set_guards_to_true(convertor, exp.operands()[i] );
        }
    } else {
        // TODO: find a more clever way of identifying guards
        if ((from_expr(ns, "", exp)).find("guard") == 1){
            //std::cout << " -> set to true " << from_expr(SSA_map[exp]) << "\n";
            convertor.set_to_true(SSA_map[exp]);

        }
    }
}
/*******************************************************************\
 
 Function:

 Purpose:

\*******************************************************************/
void dependency_checkert::convert_delta_SSA(convertort &convertor,
                                            SSA_steps_it &it1, SSA_steps_it &it2)
{
    convert_guards(convertor, it1, it2);
    convert_assignments(convertor, it1, it2);
    convert_assumptions(convertor, it1, it2);
    convert_assertions(convertor, it2);
    convert_io(convertor, it1, it2);
}
/*******************************************************************\
 
 Function:

 Purpose:

\*******************************************************************/
std::pair<bool, timet>
dependency_checkert::check_implication(dependency_checkert::SSA_steps_it c1, dependency_checkert::SSA_steps_it c2) {
    try{
        // TODO: create solver according to current settings?
        solver_optionst solver_options; // Set defaults inside
        satcheck_opensmt2t* decider = new satcheck_opensmt2t(solver_options, "implication checker", ns);
        decider->new_partition();

        convert_delta_SSA(*decider, c1, c2);

        if (VERBOSE) status() << ("RESULT");
        auto initial=timestamp();
        bool r = decider->solve();
        auto end=timestamp();
        auto duration_out = time_gap(end,initial);   
        timet duration(duration_out);
          
        status() << "SOLVER TIME FOR check_implication: " << duration_out << eom;
        // solve it
        return std::make_pair(!r, duration);

    } catch (const std::bad_alloc &e)
    {
        error ()  << "smth is wrong: " << e.what()  << eom;
        return std::make_pair(true, (timet)0);
    }
    catch (const char* e)
    {
        error () << "\nCaught exception: " << e << eom;
        return std::make_pair(true, (timet)0);
    }
    catch (const std::string &s)
    {
        error () << "\nCaught exception: " << s << eom;
        return std::make_pair(true, (timet)0);
    }
}
