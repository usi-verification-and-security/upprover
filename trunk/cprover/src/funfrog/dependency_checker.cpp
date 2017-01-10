#include <memory>

#include <time_stopping.h>
#include <expr_util.h>

#include "dependency_checker.h"
#include "expr_pretty_print.h"
#include <sstream>
#include <map>

#include <util/language.h>
#include <boost/pending/disjoint_sets.hpp>

using namespace std;
using namespace boost;

#define endl std::endl

void dependency_checkert::do_it(partitioning_target_equationt &equation){

  absolute_timet initial, temp_end;
  time_periodt duration, durationto;

  reconstruct_exec_SSA_order(equation); // the only place where partition_target_equation is used.

  initial=current_time();

  ofstream hl_list;
  hl_list.open ("__hl_list");
    for(SSA_stepst::iterator it = SSA_steps.begin(); it!=SSA_steps.end(); ++it)
    {
      if ((*it)->is_assert() && !omega.is_assertion_in_loop((*it)->source.pc)){
        asserts.push_back(it);
        //cout << "ID: " << it->source.pc->location.get_claim() << " Condition: " << from_expr(ns, "", it->cond_expr) << endl;
        instances[(*it)->source.pc->source_location.get_property_id().c_str()]++;
        hl_list << "Assertion: " << (*it)->source.pc->source_location.get_property_id().c_str() << endl;
      }
    }

    hl_list.close();

//    cout << "SSA Assertions: " << asserts.size();
//    cout << endl;

    temp_end = current_time();
    duration = temp_end - initial;
    //std::cout << "TIME FOR find_var_deps (should ~ be zero): " << (duration) << endl;

    initial=current_time();

    // TODO: this takes a lot of time. Oct.2014: optimized a little bit
    find_assert_deps();

    temp_end = current_time();
    duration = temp_end - initial;
  	std::cout << "TIME FOR find_assert_deps: " << (duration) << endl;

  	initial = current_time();

  	//TODO: FIX THIS!
  	absolute_timet to_time(find_implications());

  	temp_end = current_time();
  	duration = temp_end - initial;

  	//durationto = current_time();
  	//durationto = durationto - initial;
  	//durationto = durationto - to_time;
  	absolute_timet duration_cast(duration.get_t());
  	durationto = duration_cast - to_time;

  	time_periodt to_time_cast(to_time.get_t());

  std::cout << "TIME FOR ASSERTION OPTIMIZATIONS: " << (duration) << endl;
//  std::cout << "TIME exceeding timeouts: " << (to_time) << endl;
//  std::cout << "TIME FOR find_implications using a timeout: " << (durationto) << endl;

  //TODO: make a proper cmd-parameter
  ifstream just_dep;
  just_dep.open ("__just_hl_dep");
  if (just_dep.good()) {cout << "__just_hl_dep file is in the current directory. Exiting... " << endl; just_dep.close(); exit(1);}
  just_dep.close();

//  get_minimals();

//  initial = current_time();
//  std::cout << "TIME FOR get_minimals: " << (initial - final) << endl;
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
              if (as_string(*sym_it).find("\\guard") < 10000){ //dirty hack
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

//    cout << "Number of disjoint variable sets: " << (int)deps_ds.count_sets(equation_symbols.begin(), equation_symbols.end()) << endl;

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

//    cout << "Syntactic independencies found: " << (indeps - deps) << endl;
//    cout << "Syntactic dependencies found: " << deps << endl;

}

//static bool compare_asserts(dependency_checkert::SSA_step_reft a, dependency_checkert::SSA_step_reft b)
//{
//	return (distance(a, b) < 0);
//}

bool dependency_checkert::compare_assertions(SSA_step_reft &a, SSA_step_reft &b){
  return distance(a, b) < treshold;
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

// TODO: send equation as in parameter - requires no additional changes!
void dependency_checkert::reconstruct_exec_SSA_order(partitioning_target_equationt &equation){
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