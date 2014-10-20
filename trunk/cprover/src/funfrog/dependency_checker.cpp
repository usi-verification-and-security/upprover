#include <memory>

#include <time_stopping.h>
#include <expr_util.h>
#include <i2string.h>

#include "dependency_checker.h"
#include "expr_pretty_print.h"
#include <sstream>
#include <map>

#include <util/language.h>

#include <boost/pending/disjoint_sets.hpp>

#ifdef USE_PERIPLO
#include "solvers/satcheck_periplo.h"
#else
#include "solvers/satcheck_opensmt.h"
#endif

#define INDEPT false
#define DEPT true

#define NOTIMP false
#define IMP true

#define VERBOSE false

#define IMIN(i, j) ((int)(i)<(int)(j))?(int)(i):(int)(j)
#define IMAX(i, j) ((int)(i)<(int)(j))?(int)(j):(int)(i)

using namespace std;
using namespace boost;

#define endl std::endl

void dependency_checkert::do_it(){

  fine_timet initial, duration, durationto;

  reconstruct_exec_SSA_order();

  initial=current_time();

  ofstream hl_list;
  hl_list.open ("__hl_list");
    for(SSA_stepst::iterator it = SSA_steps.begin(); it!=SSA_steps.end(); ++it)
    {
      if ((*it)->is_assert() && !omega.is_assertion_in_loop((*it)->source.pc)){
        asserts.push_back(it);
        //cout << "ID: " << it->source.pc->location.get_claim() << " Condition: " << from_expr(ns, "", it->cond_expr) << endl;
        instances[(*it)->source.pc->location.get_claim().c_str()]++;
        hl_list << "Assertion: " << (*it)->source.pc->location.get_claim().c_str() << endl;
      }
    }

    hl_list.close();

    cout << "SSA Assertions: " << asserts.size();
    cout << endl;

  duration = current_time();
  duration = duration - initial;
  std::cout << "TIME FOR find_var_deps (should ~ be zero): " << (duration) << endl;

  initial=current_time();

  // TODO: this takes a lot of time. Oct.2014: optimized a little bit
  find_assert_deps();

  duration = current_time();
  duration = duration - initial;
  std::cout << "TIME FOR find_assert_deps: " << (duration) << endl;

  initial = current_time();

  //TODO: FIX THIS!
  fine_timet to_time(find_implications());

  duration = current_time();
  durationto = current_time();

  duration = duration - initial;
  durationto = durationto - initial;
  durationto = durationto - to_time;

  std::cout << "TIME FOR find_implications: " << (duration) << endl;
  std::cout << "TIME exceeding timeouts: " << (to_time) << endl;
  std::cout << "TIME FOR find_implications using a timeout: " << (durationto) << endl;

  //TODO: make a proper cmd-parameter
  ifstream just_dep;
  just_dep.open ("__just_hl_dep");
  if (just_dep.good()) {cout << "__just_hl_dep file is in the current directory. Exiting... " << endl; just_dep.close(); exit(1);}
  just_dep.close();

//  get_minimals();

//  initial = current_time();
//  std::cout << "TIME FOR get_minimals: " << (initial - final) << endl;
}

pair<bool, fine_timet> dependency_checkert::check_implication(SSA_step_reft &c1, SSA_step_reft &c2)
{
  try{

  std::auto_ptr<prop_convt> decider;
#ifdef USE_PERIPLO
  satcheck_periplot* opensmt = new satcheck_periplot();
#else
  satcheck_opensmtt* opensmt = new satcheck_opensmtt();
#endif
  bv_pointerst *deciderp = new bv_pointerst(ns, *opensmt);
  deciderp->unbounded_array = bv_pointerst::U_AUTO;
  decider.reset(deciderp);

  convert_delta_SSA(*decider, c1, c2);

  if (VERBOSE) status("RESULT");
  fine_timet initial, duration;
  initial=current_time();
  decision_proceduret::resultt r = (*decider).dec_solve();
  duration=current_time();
  duration = duration - initial;
#ifdef USE_PERIPLO
//  // todo
#else
delete opensmt;
#endif

  if (VERBOSE) status() << "SOLVER TIME FOR check_implication: " << (duration) << eom;

  // solve it
  switch (r)
  {
    case decision_proceduret::D_UNSATISFIABLE:
    {
      if (VERBOSE) status("UNSAT - it holds!");
      return make_pair(true, duration);
    }
    case decision_proceduret::D_SATISFIABLE:
    {
      if (VERBOSE) status("SAT - doesn't hold");
      return make_pair(false, duration);
    }

    default:
      throw "unexpected result from dec_solve()";
  }
  } catch (const bad_alloc &e)
  {
    cout  << "smth is wrong: " << e.what()  << endl;
    return make_pair(true, (fine_timet)0);
  }
  catch (const char* e)
  {
    std::cout << endl << "Caught exception: " << e << endl;
    return make_pair(true, (fine_timet)0);
  }
  catch (const std::string &s)
  {
    std::cout << endl << "Caught exception: " << s << endl;
    return make_pair(true, (fine_timet)0);
  }
}

void dependency_checkert::find_var_deps(str_disj_set &deps_ds, map<string, bool> &visited, SSA_step_reft &it1, SSA_step_reft &it2)
{

    // ============ DISJOINT SETS EDITING BEGINS

    for(SSA_stepst::iterator it = it1; it!=it2; ++it)
    {
      if ((*it)->is_assignment() || (*it)->is_assume() || (*it)->is_assert())
      {
//        if ((*it)->is_assert()){
//          cout << "  ["<< (*it)->source.pc->location.get_line() <<"]\n";
//        }
            symbol_sett all_symbols;
            symbol_sett guard_symbols;

            //get_expr_symbols((*it)->guard, all_symbols);
            get_expr_symbols((*it)->cond_expr, all_symbols);
            get_expr_symbols(SSA_map[(*it)->cond_expr], all_symbols);

            for (symbol_sett::iterator sym_it = all_symbols.begin(); sym_it != all_symbols.end(); ++sym_it){
              if (as_string(*sym_it).find("\guard") < 10000){ //dirty hack
                 //cout <<"guard symbol: " << as_string(*sym_it)  << "\n";
                  // all_symbols.erase(sym_it);
                //get_expr_symbols(SSA_map[(*it)->cond_expr], all_symbols);
              }
            }
            if (!all_symbols.empty())
            {
              std::string first_sym = as_string(*(all_symbols.begin()));
            	if (!visited[first_sym])
                {
                  deps_ds.make_set(first_sym);
                  equation_symbols.push_back(first_sym);
                  visited[first_sym] = true;
//                  cout << "I have visited a variable: " << first_sym << " ["
//                      << (visited[first_sym]?"true":"false") << "]" << endl;
                }
            }

//            else
//            {
//            	cerr << "Empty list of symbols has been found. The corresponding instruction is printed below." << endl;
//            	cerr << "Instruction type: ";
//            	if ((*it)->is_assume()) cerr << "Assumption.";
//            	else if ((*it)->is_assignment()) cerr << "Assignment.";
//            	else cerr << "Neither assertion nor assignment.";
//            	cerr << endl;
//            	cerr << "Guard: " << from_expr(ns, "", (*it)->guard) << endl;
//            	cerr << "Condition: " << from_expr(ns, "", (*it)->cond_expr) << endl;
//            	cerr << "High level code line number: " << (*it)->source.pc->location.as_string() << endl;
//            }

            for (symbol_sett::iterator sym_it = all_symbols.begin(); sym_it != all_symbols.end(); ++sym_it)
            {
              std::string next_sym = as_string(*sym_it);
            	if (!visited[next_sym])
              {
                equation_symbols.push_back(next_sym);
                deps_ds.make_set(next_sym);
                visited[next_sym] = true;
//                cout << "I have visited a variable: " << next_sym << " ["
//                    << (visited[next_sym]?"true":"false") << "]" << endl;
              }
            	//cout << "Merging: " << as_string(*(all_symbols.begin())) << " and " <<  next_sym <<"\n";
              deps_ds.union_set(as_string(*(all_symbols.begin())), next_sym);
            	//string x = deps_ds->find_set(as_string(*sym_it));
            	//cout << "Printing test of variable: " << x << endl;
            	//exit(1);
            }
        }
    }

    //FIXME: Determine if compression is needed for greater efficiency
    //deps_ds.compress_sets(equation_symbols.begin(), equation_symbols.end());

    cout << "Number of disjoint variable sets: " << (int)deps_ds.count_sets(equation_symbols.begin(), equation_symbols.end()) << endl;

}

void dependency_checkert::find_assert_deps()
{
    int deps=0;
    int indeps=0;
    bool doubleforbreak;

    rank_t rank_map;
    parent_t parent_map;

    associative_property_map<rank_t> rank_pmap(rank_map);
    associative_property_map<parent_t> parent_pmap(parent_map);

    str_disj_set deps_ds(rank_pmap, parent_pmap);
    map<string, bool> visited;

    find_var_deps(deps_ds, visited, asserts[0], asserts[asserts.size()-1]);

    for (unsigned i = 0; i < asserts.size(); i++)
    {
      SSA_step_reft& assert_1 = asserts[i];
      symbol_sett first_symbols;
      get_expr_symbols((*assert_1)->guard, first_symbols);
      get_expr_symbols((*assert_1)->cond_expr, first_symbols);

      //unsigned int lend = IMIN(i + (treshold), asserts.size());

      for (unsigned j = i + 1; j < asserts.size(); j++)
      {
        indeps++;
        SSA_step_reft& assert_2 = asserts[j];
        if (!compare_assertions(assert_1, assert_2))
          continue;

        symbol_sett second_symbols;
        get_expr_symbols((*assert_2)->guard, second_symbols);
        get_expr_symbols((*assert_2)->cond_expr, second_symbols);
        doubleforbreak = false;
        for (symbol_sett::iterator first_symit = first_symbols.begin();
            (first_symit != first_symbols.end() && (!doubleforbreak));
            ++first_symit)
          {
        	for (symbol_sett::iterator second_symit = second_symbols.begin();
        	    (second_symit != second_symbols.end() && (!doubleforbreak));
        	    ++second_symit)
            {
        	    if (visited[as_string(*first_symit)] && visited[as_string(*second_symit)])
                if (deps_ds.find_set(as_string(*first_symit)) == deps_ds.find_set(as_string(*second_symit)) )
                {
                  assert_deps[assert_1][assert_2] = DEPT;
                  //assert_deps[assert_2][assert_1] = DEPT;
                  doubleforbreak = true;
                  deps++;
//                  cout << "The following assertions are dependent!" << endl;
//                  cout << from_expr(ns, "", (*assert_1)->cond_expr) << endl;
//                  cout << from_expr(ns, "", (*assert_2)->cond_expr) << endl;
                }
            }
          }
        }
    }

    cout << "Syntactic independencies found: " << (indeps - deps) << endl;
    cout << "Syntactic dependencies found: " << deps << endl;

}

//static bool compare_asserts(dependency_checkert::SSA_step_reft a, dependency_checkert::SSA_step_reft b)
//{
//	return (distance(a, b) < 0);
//}

bool dependency_checkert::compare_assertions(SSA_step_reft &a, SSA_step_reft &b){
  return distance(a, b) < treshold;
}

long dependency_checkert::find_implications()
{
  long true_time, false_time, to_time;
  true_time = 0;
  false_time = 0;
  to_time = 0;
  //bool mustprint = false;
  unsigned notdisc = 0;
  unsigned discarded = 0;
  int checks=0;
  int impchecks=0;
  vector<bool> stronger(asserts.size(), true);
  vector<bool> weaker(asserts.size(), true);
  
    /*
    cout << "Printing assertions before ordering." << endl;
    for (it = asserts.begin(); it != asserts.end(); it++)
    {
    	cout << from_expr(ns, "", (*it)->cond_expr) << endl;
    }
    */

    //sort(asserts.begin(), asserts.end(), compare_asserts);

    /*
    cout << "Printing assertions after ordering." << endl;
    for (it = asserts.begin(); it != asserts.end(); it++)
    {
    	cout << from_expr(ns, "", (*it)->cond_expr) << endl;
    }
    */

  ofstream hl_may_impl;
  hl_may_impl.open ("__hl_may_impl");

  for (unsigned i = 0; i < asserts.size(); i++)
  {
    SSA_step_reft& assert_1 = asserts[i];
    //unsigned int lstart = IMAX(0, i - (treshold - 1));
	  //unsigned int lend = IMIN(i + (treshold), asserts.size());
    for (unsigned j = i+1; j < asserts.size(); j++)
    {
      checks++;
      pair<bool, fine_timet> checkres;
      SSA_step_reft& assert_2 = asserts[j];
      if (compare_assertions(assert_1, assert_2)
          && assert_deps[assert_1][assert_2] == DEPT
          )
      {
        impchecks++;
        if (VERBOSE)
        {
          cout << "Comparing the assertions " <<
            from_expr(ns, "", (*assert_1)->cond_expr) << " and " <<
            from_expr(ns, "", (*assert_2)->cond_expr) << endl;
        }
                checkres = check_implication(assert_1, assert_2);

        if (checkres.first == true)
        {
          true_time = true_time + checkres.second.get_t();
          if (VERBOSE) {cout << "check_implication returned TRUE" << endl;}
          if (checkres.second.get_t() <= impl_timeout)
          {
            assert_imps[assert_1][assert_2] = IMP;
            if (VERBOSE)
            {
              std::cout << "Adding the assertion implication \n (" <<
                from_expr(ns, "", (*assert_1)->cond_expr) << ") [" << (*assert_1)->source.pc->location.get_line() << "] [stronger] \n => \n (" <<
                from_expr(ns, "", (*assert_2)->cond_expr) << ") [" << (*assert_2)->source.pc->location.get_line() << "] [weaker]" << endl;
            }

            weaker[i] = false;
            stronger[j] = false;
            hl_may_impl << (*assert_1)->source.pc->location.get_claim() << " " <<
                (*assert_2)->source.pc->location.get_claim() << " " <<
                distance(SSA_steps.begin(), assert_1) << " " <<
                distance(SSA_steps.begin(), assert_2) << endl;

            discarded++;
          }
          else
          {
            notdisc++;
          }
        }
        else
        {
        	false_time = false_time + checkres.second.get_t();
        	if (VERBOSE) { cout << "check_implication returned FALSE" << endl;}
        }
        if (checkres.second.get_t() > impl_timeout)
        {
        	long exceeding = checkres.second.get_t() - impl_timeout;
        	cout << "Timeout " << (impl_timeout/1000) << "." <<
        	                      (impl_timeout%1000)/10 << " exceeded of " <<
        	                      (exceeding/1000) << "." <<
        	                      (exceeding%1000)/10 << " seconds." << endl;
            to_time = to_time + exceeding;
        }
      }
    }
  }

//    std::cout << "Printing assertion implications:" << endl;
//    for (map<SSA_step_reft,map<SSA_step_reft,bool> >::iterator dep_first_it = assert_imps.begin(); dep_first_it != assert_imps.end(); ++dep_first_it)
//      for (map<SSA_step_reft,bool>::iterator dep_second_it = dep_first_it->second.begin(); dep_second_it != dep_first_it->second.end(); ++dep_second_it)
//      std::cout << "(" << from_expr(ns, "", dep_first_it->first->cond_expr) << " => " << from_expr(ns, "", dep_second_it->first->cond_expr) << ")" << endl;

  hl_may_impl.close();

  cout << "Discarded assertions: " << discarded << endl;
  if (notdisc > 0) cout << "WARNING: " << notdisc << " true implications exceeded timeout!" << endl;

  cout << "Total number of implication checks: " << impchecks << endl;
  cout << "Total number of comparisons: " << checks << endl;

  for (int i = asserts.size() - 1; i >= 0; i--)
  //for (unsigned i = 0; i < asserts.size(); i++)
  {
    if (weaker[i] == true)
	  {
		  SSA_step_reft& removable = asserts[i];
      cout << "Removing << " << (*removable)->source.pc->location.get_line() << "\n";
      (*removable)->ignore = true;
	  }
  }
  try{
    ofstream hl_stronger;
    ofstream hl_weaker;
    hl_stronger.open ("__hl_stronger");
    hl_weaker.open ("__hl_weaker");
    int hldiscardable = 0;
    for (int i = asserts.size() - 1; i >= 0; i--){
      SSA_step_reft& ass = asserts[i];
      if (weaker[i] == true)
        hl_weaker << (*ass)->source.pc->location.get_claim().c_str() << endl;
      if (stronger[i] == true)
        hl_stronger << (*ass)->source.pc->location.get_claim().c_str() << endl;
    }

    hl_stronger.close();
    hl_weaker.close();
  }  catch (const bad_alloc &e)
  {
    cout  << "smth is very wrong: " << e.what()  << endl;

  }
  return to_time;

}

void dependency_checkert::get_minimals()
{
  // TODO: it doesn't seem working
  map<SSA_step_reft,int> inDegree;

    for (map<SSA_step_reft,map<SSA_step_reft,bool> >::iterator dep_first_it = assert_imps.begin(); dep_first_it != assert_imps.end(); ++dep_first_it)
      for (map<SSA_step_reft,bool>::iterator dep_second_it = dep_first_it->second.begin(); dep_second_it != dep_first_it->second.end(); ++dep_second_it)
        inDegree[dep_second_it->first]++;

    map<SSA_step_reft, int>::iterator degree_it;
    for (degree_it = inDegree.begin(); degree_it != inDegree.end(); degree_it++)
    {
      if (degree_it->second == 0) toCheck[degree_it->first] = true;
    }

}

void dependency_checkert::print_SSA_steps_infos()
{
//TODO: integrate with new CProver
/*  map<string,map<string,bool> > var_deps;

  //printf("Sono dentro la dependency analysis!\n");
  std::cout << endl << "Printing SSA data" << endl << endl;
    for(SSA_stepst::iterator it = SSA_steps.begin(); it!=SSA_steps.end(); ++it)
    {
      it->output(ns, std::cout);
      std::cout << "Andrea's data:\n";
      std::cout << "Guard = " << from_expr(ns, "", it->guard) << endl;
      if (it->is_assignment())
      {
            std::cout << "  Type = ASSIGNMENT" << endl;
            std::cout << "  Assignment type = ";
            if (it->assignment_type == symex_targett::HIDDEN) std::cout << "HIDDEN" << endl;
            else if (it->assignment_type == symex_targett::STATE) std::cout << "STATE" << endl;
            else std::cout << "NOT EXPECTED" << endl;
            std::cout << "  Condition expression = " << from_expr(ns, "", it->cond_expr) << endl;
            std::cout << "Symbols in the expression: ";
            print_expr_symbols(std::cout, it->cond_expr);
            std::cout << endl;
            std::cout << "left-hand side: " << from_expr(ns, "", it->ssa_lhs) << endl;
            std::cout << "Symbols in the left-hand side: ";
            print_expr_symbols(std::cout, it->ssa_lhs);
            std::cout << endl;
            std::cout << "right-hand side: " << from_expr(ns, "", it->ssa_rhs) << endl;
            std::cout << "Symbols in the right-hand side: ";
            print_expr_symbols(std::cout, it->ssa_rhs);
            std::cout << endl;
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
                  std::cout << "Dependency " << variable_name(*lhs_it) << " <- " << variable_name(*rhs_it) << " is being added." << endl;
                  var_deps[lid][rid] = DEPT;
                }
                for (symbol_sett::iterator guard_it = guard_symbols.begin(); guard_it != guard_symbols.end(); ++guard_it)
                {
                  string gid = as_string(*guard_it);
                  std::cout << "Dependency " << variable_name(*lhs_it) << " <- " << variable_name(*guard_it) << " is being added." << endl;
                  var_deps[lid][gid] = DEPT;
                }
            }
        }
      else if (it->is_assert())
      {
        std::cout << "  Type = ASSERT" << endl;
        std::cout << "  Condition expression = " << from_expr(ns, "", it->cond_expr) << endl;
        std::cout << "  Comment = " << it->comment << endl;
      }
      else if (it->is_assume())
      {
        std::cout << "  Type = ASSUME" << endl;
        std::cout << "  Condition expression = " << from_expr(ns, "", it->cond_expr) << endl;
      }
      else if (it->is_location())
      {
        std::cout << "  Type = LOCATION" << endl;
      }
      else if (it->is_output())
      {
        std::cout << "  Type = OUTPUT" << endl;
      }
      else
      {
        std::cout << "  Type = NOT EXPECTED" << endl;
      }
        if(it->source.is_set)
        {
          std::cout << "  Thread = " << it->source.thread_nr << endl;
          if(it->source.pc->location.is_not_nil())
            std::cout << "  Location = " << it->source.pc->location << endl;
          else
            std::cout << endl;
        }
        if (it->cond_expr.has_operands())
        {
            std::cout << "  Operands:" << endl;

            int k = 0;
            Forall_operands(op, it->cond_expr)
            {
            std::cout << "    Op[" << k << "] = ";
            //expr_pretty_print(tempstr, *op, 2);
            print_expr_operands(std::cout, *op, 2);
            k++;
            }

        }
        std::cout << endl;
    }
    std::cout << "Printing dependencies:" << endl;
    map<string,map<string,bool> >::iterator dep_it;
    for ( dep_it=var_deps.begin() ; dep_it != var_deps.end(); dep_it++ )
    {
      std::cout << variable_name((*dep_it).first) << " <- ";
      print_dependents((*dep_it).second, std::cout);
      std::cout << endl;
    }
    */
}

void dependency_checkert::print_dependents(map<string,bool> dependents, std::ostream &out)
{
  map<string,bool>::iterator it;
  int count = 0;
  for ( it=dependents.begin() ; it != dependents.end(); it++ )
  {
    if ((*it).second == true) {if (count > 0) out << ", "; out << variable_name((*it).first); count++;}
  }
}

std::string dependency_checkert::variable_name(dstring name)
{
  return variable_name(as_string(name));
}

std::string dependency_checkert::variable_name(std::string name)
{
  return name.substr(name.find_last_of(":") + 1, 10);
}

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

void dependency_checkert::print_expr_symbols(std::ostream &out, exprt expr)
{
    symbol_sett s;
    get_expr_symbols(expr, s);
    print_expr_symbols(out, s);
}

void dependency_checkert::print_expr_symbols(std::ostream &out, symbol_sett& s)
{
    for (symbol_sett::iterator it = s.begin(); it != s.end(); ++it)
    {
      out << variable_name(*it) << " ";
    }
    //s.clear();
}

void dependency_checkert::print_expr_operands(std::ostream &out, exprt expr, int indent)
{
  if (expr.has_operands())
  {
    expr_pretty_printt pretty(out);
    pretty(expr);
  }
  else out << from_expr(ns, "", expr) << endl;
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
    for(SSA_stepst::iterator it = SSA_steps.begin(); it!=SSA_steps.end(); ++it)
    {
      (*it)->output(ns, std::cout);
    }
}

void dependency_checkert::convert_delta_SSA(prop_convt &prop_conv,
    SSA_step_reft &it1, SSA_step_reft &it2)
{
  convert_guards(prop_conv, it1, it2);
  convert_assignments(prop_conv, it1, it2);
  convert_assumptions(prop_conv, it1, it2);
  convert_assertions(prop_conv, it2);
  convert_io(prop_conv, it1, it2);
}

void dependency_checkert::deep_convert_guards(prop_convt &prop_conv, exprt exp){
  if (exp.has_operands())
  {
    for (unsigned i = 0; i < exp.operands().size(); i++){
      deep_convert_guards(prop_conv, exp.operands()[i] );
    }
  } else {
    // TODO: find a more clever way of identifying guards
    if ((from_expr(ns, "", exp)).find("guard") == 1){
      //std::cout << " -> converting " << from_expr(SSA_map[exp]) << "\n";
      prop_conv.convert(SSA_map[exp]);
    }
  }
}

void dependency_checkert::set_guards_to_true(prop_convt &prop_conv, exprt exp){
  if (exp.has_operands())
  {
    for (unsigned i = 0; i < exp.operands().size(); i++){
      set_guards_to_true(prop_conv, exp.operands()[i] );
    }
  } else {
    // TODO: find a more clever way of identifying guards
    if ((from_expr(ns, "", exp)).find("guard") == 1){
      //std::cout << " -> set to true " << from_expr(SSA_map[exp]) << "\n";
      prop_conv.set_to_true(SSA_map[exp]);
    }
  }
}

void dependency_checkert::convert_assignments(
    prop_convt &prop_conv, SSA_step_reft &it1, SSA_step_reft &it2)
{
  SSA_step_reft it=it1;
  while(it!=it2){
    it++;

    if((*it)->is_assignment() && !(*it)->ignore)
    {
      //std::cout << "convert assign :" << from_expr(ns, "", (*it)->cond_expr) <<"\n";
      prop_conv.set_to_true((*it)->cond_expr);
    }
  }
}

void dependency_checkert::convert_guards(
  prop_convt &prop_conv, SSA_step_reft &it1, SSA_step_reft &it2)
{
  SSA_step_reft it=it1;
  SSA_step_reft it3=it2;
  it3++;

  while(it!=it3){
      if ((*it)->cond_expr.is_nil() || (*it)->ignore){
        (*it)->guard_literal=const_literal(false);
      }
      else {
        //std::cout << "convert guard: " << from_expr(ns, "", (*it)->cond_expr) <<"\n";
        prop_conv.convert((*it)->cond_expr);
        //deep_convert_guards(prop_conv, ((*it)->cond_expr));
      }
    it++;
  }
}

void dependency_checkert::convert_assumptions(
  prop_convt &prop_conv, SSA_step_reft &it1, SSA_step_reft &it2)
{
  SSA_step_reft it=it1;
  while(it!=it2)
  {
    if(((*it)->is_assume() || ((*it)->is_assert() && it ==it1)) && !(*it)->ignore)
    {
       //std::cout << "convert assume :" << from_expr(ns, "", (*it)->cond_expr) <<"\n";
       prop_conv.set_to_true((*it)->cond_expr);
       set_guards_to_true(prop_conv, ((*it)->cond_expr));
    }
    it++;
  }
}

void dependency_checkert::convert_assertions(
  prop_convt &prop_conv, SSA_step_reft &it2)
{
  assert((*it2)->is_assert());
  //std::cout << "convert assert :" << from_expr(ns, "", (*it2)->cond_expr) <<"\n";
  set_guards_to_true(prop_conv, ((*it2)->cond_expr));
  prop_conv.set_to_false((*it2)->cond_expr);
}

void dependency_checkert::convert_io(
    prop_convt &prop_conv, SSA_step_reft &it1, SSA_step_reft &it2)
{
  unsigned io_count=0;
  SSA_step_reft it=it1;
  SSA_step_reft it3=it2;
  it3++;

  while (it!=it3){
      for(std::list<exprt>::const_iterator
          o_it=(*it)->io_args.begin();
          o_it!=(*it)->io_args.end();
          o_it++)
      {
        exprt tmp=*o_it;
        if(tmp.is_constant() ||
           tmp.id()==ID_string_constant)
          (*it)->converted_io_args.push_back(tmp);
        else
        {
          symbol_exprt symbol;
          symbol.type()=tmp.type();
          symbol.set_identifier("symex::io::"+i2string(io_count++));
          prop_conv.set_to(equal_exprt(tmp, symbol), true);
          (*it)->converted_io_args.push_back(symbol);
        }
      }
    it++;
  }
}

void dependency_checkert::reconstruct_exec_SSA_order(){
  const SSA_steps_orderingt& SSA_steps = equation.get_steps_exec_order();
  for(SSA_steps_orderingt::const_iterator
      it=SSA_steps.begin();
      it!=SSA_steps.end();
      it++)
  {
    symex_target_equationt::SSA_stept& SSA_step=**it;
    this->SSA_steps.push_back(&SSA_step);
    SSA_map[SSA_step.ssa_full_lhs] = SSA_step.cond_expr;
  }
}
