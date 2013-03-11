
#include <memory>

#include <time_stopping.h>
#include <expr_util.h>
#include <i2string.h>

#include "partitioning_slice.h"
#include "dependency_checker.h"
#include "expr_pretty_print.h"
#include "solvers/satcheck_opensmt.h"
#include <sstream>
#include <map>

#define INDEPT false
#define DEPT true

#define NOTIMP false
#define IMP true

using namespace std;

void dependency_checkert::do_it(){
  fine_timet initial, final;
  initial=current_time();

  find_var_deps();

  final = current_time();
  std::cout << "TIME FOR find_var_deps: " << time2string(final - initial) << std::endl;

  find_assert_deps();

  initial = current_time();
  std::cout << "TIME FOR find_assert_deps: " << time2string(initial - final) << std::endl;

  find_implications();

  final = current_time();
  std::cout << "TIME FOR find_implications: " << time2string(final - initial) << std::endl;

  get_minimals();

  initial = current_time();
  std::cout << "TIME FOR get_minimals: " << time2string(initial - final) << std::endl;
}

bool dependency_checkert::check_implication(SSA_step_reft &c1, SSA_step_reft &c2)
{
  std::auto_ptr<prop_convt> decider;
  satcheck_opensmtt* opensmt = new satcheck_opensmtt();
  bv_pointerst *deciderp = new bv_pointerst(ns, *opensmt);
  deciderp->unbounded_array = bv_pointerst::U_AUTO;
  decider.reset(deciderp);

  convert_delta_SSA(*decider, c1, c2);

  status("RESULT");
  fine_timet before, after;
  before=current_time();
  decision_proceduret::resultt r = (*decider).dec_solve();
  after=current_time();
  status(std::string("SOLVER TIME: ") + time2string(after-before));

  // solve it
  switch (r)
  {
    case decision_proceduret::D_UNSATISFIABLE:
    {
      status("UNSAT - it holds!");
      return true;
    }
    case decision_proceduret::D_SATISFIABLE:
    {
      status("SAT - doesn't hold");
      return false;
    }

    default:
      throw "unexpected result from dec_solve()";
  }
}

void dependency_checkert::find_var_deps(bool ENABLE_TC)
{
    int mapcount = 0;
    for(symex_target_equationt::SSA_stepst::iterator it = equation.SSA_steps.begin(); it!=equation.SSA_steps.end(); ++it)
    {
      //it->output(ns, std::cout);
      if ((it->is_assignment()) || (it->is_assume()))
      {
            symbol_sett all_symbols;

            get_expr_symbols(it->guard_expr, all_symbols);
            get_expr_symbols(it->cond_expr, all_symbols);

            //PRINT
            //std::cout << "All symbols: ";
            //print_expr_symbols(std::cout, all_symbols);
            //std::cout << std::endl;

            for (symbol_sett::iterator first_it = all_symbols.begin(); first_it != all_symbols.end(); ++first_it)
            {
              string first_id = first_it->as_string();
                for (symbol_sett::iterator second_it = all_symbols.begin(); second_it != all_symbols.end(); ++second_it)
                {
                  mapcount++;
                  //cout << "Ho fatto " << mapcount << " assegnamenti." << endl;
                  string second_id = second_it->as_string();
                  //std::cout << "Dependency " << variable_name(*first_it) << " <- " << variable_name(*second_it) << " is being added." << std::endl;
                  if ((!label[first_id]) && (!label[second_id]))
                  {
                	  last_label++;
                	  label[first_id] = new int;
                	  *label[first_id] = last_label;
                	  label[second_id] = label[first_id];
                  }
                  else if (!label[first_id])
                	  label[first_id] = label[second_id];
                  else if (!label[second_id])
                	  label[second_id] = label[first_id];
                  else
                	  *label[second_id] = *label[first_id];

                  var_deps[first_id][second_id] = DEPT;
                  var_deps[second_id][first_id] = DEPT;
                }
            }
        }
    }
//    std::cout << "Printing dependencies:" << std::endl;
//    map<string,map<string,bool> >::iterator dep_it;
//    for ( dep_it=var_deps.begin() ; dep_it != var_deps.end(); dep_it++ )
//    {
//      std::cout << variable_name((*dep_it).first) << " <- ";
//      print_dependents((*dep_it).second, std::cout);
//      std::cout << std::endl;
//    }

    if (ENABLE_TC)
    {
      map<string,map<string,bool> >::iterator first_it, second_it, third_it;
      for (first_it = var_deps.begin(); first_it != var_deps.end(); first_it++)
      {
        for (second_it = var_deps.begin(); second_it != var_deps.end(); second_it++)
        {
          for (third_it = var_deps.begin(); third_it != var_deps.end(); third_it++)
          {
            if ((first_it->first != second_it->first) && (second_it->first != third_it->first) && (first_it->first != third_it->first))
            if ((var_deps[first_it->first][second_it->first] == DEPT) && (var_deps[second_it->first][third_it->first] == DEPT))
            {
              var_deps[first_it->first][third_it->first] = DEPT;
              var_deps[third_it->first][first_it->first] = DEPT;
              //PRINTING
              //std::cout << "Since the pairs (" << variable_name(first_it->first) << ", " << variable_name(second_it->first) << ") and ("
              //     << variable_name(second_it->first) << ", " << variable_name(third_it->first) << ") have been added, " << std::endl;
              //std::cout << "then for transitivity the pair (" << variable_name(first_it->first) << ", " << variable_name(third_it->first) << ") is added." << std::endl;
            }
          }
        }
      }
    }
}

void dependency_checkert::find_assert_deps()
{
    for(symex_target_equationt::SSA_stepst::iterator it = equation.SSA_steps.begin(); it!=equation.SSA_steps.end(); ++it)
    {
      if (it->is_assert() && !omega.is_assertion_in_loop(it->source.pc)){
        asserts.push_back(it);
      }
    }
//    Printing
//    std::cout << "Printing assertions:" << std::endl;
//    map<SSA_step_reft, bool>::iterator asserts_it;
//    for (asserts_it = asserts.begin(); asserts_it != asserts.end(); asserts_it++)
//    {
//      (asserts_it->first)->output(ns, std::cout);
//    }

    symbol_sett first_symbols, second_symbols;

    for (unsigned i = 0; i < asserts.size(); i++)
    {
      first_symbols.clear();
      get_expr_symbols(asserts[i]->guard_expr, first_symbols);
      get_expr_symbols(asserts[i]->cond_expr, first_symbols);

      for (unsigned j = i + 1; j < asserts.size(); j++)
      {
        SSA_step_reft& ass_1 = asserts[i];
        SSA_step_reft& ass_2 = asserts[j];
        if (!compare_assertions(ass_1, ass_2))
          continue;
        second_symbols.clear();
        get_expr_symbols(asserts[j]->guard_expr, second_symbols);
        get_expr_symbols(asserts[j]->cond_expr, second_symbols);

        for (symbol_sett::iterator first_symit = first_symbols.begin(); first_symit != first_symbols.end(); ++first_symit)
          {
            for (symbol_sett::iterator second_symit = second_symbols.begin(); second_symit != second_symbols.end(); ++second_symit)
            {
              //if (var_deps[first_symit->as_string()][second_symit->as_string()] == DEPT)
            if (label[first_symit->as_string()] && label[second_symit->as_string()])
              if (*label[first_symit->as_string()] == *label[second_symit->as_string()])
              {
                assert_deps[asserts[i]][asserts[j]] = DEPT;
                assert_deps[asserts[j]][asserts[i]] = DEPT;
              }
            }
          }
        }
    }

    /*
    std::cout << "Printing assertion dependencies:" << std::endl;
    for (map<SSA_step_reft,map<SSA_step_reft,bool> >::iterator dep_first_it = assert_deps.begin(); dep_first_it != assert_deps.end(); ++dep_first_it)
      for (map<SSA_step_reft,bool>::iterator dep_second_it = dep_first_it->second.begin(); dep_second_it != dep_first_it->second.end(); ++dep_second_it)
        if (assert_deps[dep_first_it->first][dep_second_it->first] == DEPT)  std::cout << "(" << from_expr(ns, "", dep_first_it->first->cond_expr) << " <-> " << from_expr(ns, "", dep_second_it->first->cond_expr) << ")" << std::endl;
    */

}

//static bool compare_asserts(dependency_checkert::SSA_step_reft a, dependency_checkert::SSA_step_reft b)
//{
//	return (distance(a, b) < 0);
//}

bool dependency_checkert::compare_assertions(SSA_step_reft &a, SSA_step_reft &b){
  return distance(a, b) < treshold;
}

void dependency_checkert::find_implications()
{
  bool mustprint = false;
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

  for (unsigned i = 0; i < asserts.size(); i++)
  {
    for (unsigned j = 0; j < asserts.size(); j++)
    {
      SSA_step_reft& ass_1 = asserts[i];
      SSA_step_reft& ass_2 = asserts[j];
      if (compare_assertions(ass_1, ass_2) &&
          assert_deps[ass_1][ass_2] == DEPT){
        cout << "Comparing the assertions " <<
    			from_expr(ns, "", ass_1->cond_expr) << " and " <<
    			from_expr(ns, "", ass_2->cond_expr) << endl;
        if (check_implication(ass_1, ass_2) == true)
        {
          cout << "check_implication returned TRUE" << endl;
          assert_imps[ass_1][ass_2] = IMP;
          std::cout << "Adding the assertion implication (" <<
          from_expr(ns, "", ass_1->cond_expr) << " => " <<
          from_expr(ns, "", ass_2->cond_expr) << ")" << std::endl;

          equation.SSA_steps.erase(ass_2);
          asserts.erase(asserts.begin()+j);

        }
        else cout << "check_implication returned FALSE" << endl;
      }
    }
  }

//    std::cout << "Printing assertion implications:" << std::endl;
//    for (map<SSA_step_reft,map<SSA_step_reft,bool> >::iterator dep_first_it = assert_imps.begin(); dep_first_it != assert_imps.end(); ++dep_first_it)
//      for (map<SSA_step_reft,bool>::iterator dep_second_it = dep_first_it->second.begin(); dep_second_it != dep_first_it->second.end(); ++dep_second_it)
//      std::cout << "(" << from_expr(ns, "", dep_first_it->first->cond_expr) << " => " << from_expr(ns, "", dep_second_it->first->cond_expr) << ")" << std::endl;

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
  map<string,map<string,bool> > var_deps;

  //printf("Sono dentro la dependency analysis!\n");
  std::cout << std::endl << "Printing SSA data" << std::endl << std::endl;
    for(symex_target_equationt::SSA_stepst::iterator it = equation.SSA_steps.begin(); it!=equation.SSA_steps.end(); ++it)
    {
      it->output(ns, std::cout);
      std::cout << "Andrea's data:\n";
      std::cout << "Guard = " << from_expr(ns, "", it->guard_expr) << std::endl;
      if (it->is_assignment())
      {
            std::cout << "  Type = ASSIGNMENT" << std::endl;
            std::cout << "  Assignment type = ";
            if (it->assignment_type == symex_targett::HIDDEN) std::cout << "HIDDEN" << std::endl;
            else if (it->assignment_type == symex_targett::STATE) std::cout << "STATE" << std::endl;
            else std::cout << "NOT EXPECTED" << std::endl;
            std::cout << "  Condition expression = " << from_expr(ns, "", it->cond_expr) << std::endl;
            std::cout << "Symbols in the expression: ";
            print_expr_symbols(std::cout, it->cond_expr);
            std::cout << std::endl;
            std::cout << "left-hand side: " << from_expr(ns, "", it->lhs) << std::endl;
            std::cout << "Symbols in the left-hand side: ";
            print_expr_symbols(std::cout, it->lhs);
            std::cout << std::endl;
            std::cout << "right-hand side: " << from_expr(ns, "", it->rhs) << std::endl;
            std::cout << "Symbols in the right-hand side: ";
            print_expr_symbols(std::cout, it->rhs);
            std::cout << std::endl;
            symbol_sett lhs_symbols, rhs_symbols, guard_symbols;
            get_expr_symbols(it->lhs, lhs_symbols);
            get_expr_symbols(it->rhs, rhs_symbols);
            get_expr_symbols(it->guard_expr, guard_symbols);
            dstring temp;
            for (symbol_sett::iterator lhs_it = lhs_symbols.begin(); lhs_it != lhs_symbols.end(); ++lhs_it)
            {
              string lid = lhs_it->as_string();
                for (symbol_sett::iterator rhs_it = rhs_symbols.begin(); rhs_it != rhs_symbols.end(); ++rhs_it)
                {
                  string rid = rhs_it->as_string();
                  std::cout << "Dependency " << variable_name(*lhs_it) << " <- " << variable_name(*rhs_it) << " is being added." << std::endl;
                  var_deps[lid][rid] = DEPT;
                }
                for (symbol_sett::iterator guard_it = guard_symbols.begin(); guard_it != guard_symbols.end(); ++guard_it)
                {
                  string gid = guard_it->as_string();
                  std::cout << "Dependency " << variable_name(*lhs_it) << " <- " << variable_name(*guard_it) << " is being added." << std::endl;
                  var_deps[lid][gid] = DEPT;
                }
            }
        }
      else if (it->is_assert())
      {
        std::cout << "  Type = ASSERT" << std::endl;
        std::cout << "  Condition expression = " << from_expr(ns, "", it->cond_expr) << std::endl;
        std::cout << "  Comment = " << it->comment << std::endl;
      }
      else if (it->is_assume())
      {
        std::cout << "  Type = ASSUME" << std::endl;
        std::cout << "  Condition expression = " << from_expr(ns, "", it->cond_expr) << std::endl;
      }
      else if (it->is_location())
      {
        std::cout << "  Type = LOCATION" << std::endl;
      }
      else if (it->is_output())
      {
        std::cout << "  Type = OUTPUT" << std::endl;
      }
      else
      {
        std::cout << "  Type = NOT EXPECTED" << std::endl;
      }
        if(it->source.is_set)
        {
          std::cout << "  Thread = " << it->source.thread_nr << std::endl;
          if(it->source.pc->location.is_not_nil())
            std::cout << "  Location = " << it->source.pc->location << std::endl;
          else
            std::cout << std::endl;
        }
        if (it->cond_expr.has_operands())
        {
            std::cout << "  Operands:" << std::endl;

            int k = 0;
            Forall_operands(op, it->cond_expr)
            {
            std::cout << "    Op[" << k << "] = ";
            //expr_pretty_print(tempstr, *op, 2);
            print_expr_operands(std::cout, *op, 2);
            k++;
            }

        }
        std::cout << std::endl;
    }
    std::cout << "Printing dependencies:" << std::endl;
    map<string,map<string,bool> >::iterator dep_it;
    for ( dep_it=var_deps.begin() ; dep_it != var_deps.end(); dep_it++ )
    {
      std::cout << variable_name((*dep_it).first) << " <- ";
      print_dependents((*dep_it).second, std::cout);
      std::cout << std::endl;
    }
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
  return variable_name(name.as_string());
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
  else out << from_expr(ns, "", expr) << std::endl;
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
  //printf("Sono dentro la stampa degli SSA steps!\n");
    for(symex_target_equationt::SSA_stepst::iterator it = equation.SSA_steps.begin(); it!=equation.SSA_steps.end(); ++it)
    {
      it->output(ns, std::cout);
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

void dependency_checkert::convert_assignments(
    prop_convt &prop_conv, SSA_step_reft &it1, SSA_step_reft &it2)
{
  SSA_step_reft it=it1;
  while(it!=it2){
    it++;

    if(it->is_assignment() && !it->ignore)
    {
      //std::cout << "convert assign :" << from_expr(ns, "", it->cond_expr) <<"\n";
      prop_conv.set_to_true(it->cond_expr);
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
      if (it->cond_expr.is_nil() || it->ignore){
        it->guard_literal=const_literal(false);
      }
      else {
        //std::cout << "convert guard :" << from_expr(ns, "", it->cond_expr) <<"\n";
        prop_conv.convert(it->cond_expr);
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
    if((it->is_assume() || it->is_assert()) && !it->ignore)
    {
       //std::cout << "convert assume :" << from_expr(ns, "", it->cond_expr) <<"\n";
       prop_conv.set_to_true(it->cond_expr);
    }
    it++;
  }
}

void dependency_checkert::convert_assertions(
  prop_convt &prop_conv, SSA_step_reft &it2)
{
  assert(it2->is_assert());
  //std::cout << "convert assert :" << from_expr(ns, "", it2->cond_expr) <<"\n";
  prop_conv.set_to_false(it2->cond_expr);
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
          o_it=it->io_args.begin();
          o_it!=it->io_args.end();
          o_it++)
      {
        exprt tmp=*o_it;
        if(tmp.is_constant() ||
           tmp.id()==ID_string_constant)
          it->converted_io_args.push_back(tmp);
        else
        {
          symbol_exprt symbol;
          symbol.type()=tmp.type();
          symbol.set_identifier("symex::io::"+i2string(io_count++));
          prop_conv.set_to(equality_exprt(tmp, symbol), true);
          it->converted_io_args.push_back(symbol);
        }
      }
    it++;
  }
}

/*
 void dependency_checkert::find_implications()
{
  vector<SSA_step_reft> asserts;
  bool mustprint = false;
    for(symex_target_equationt::SSA_stepst::iterator it = equation.SSA_steps.begin(); it!=equation.SSA_steps.end(); ++it)
    {
      if (it->is_assert()) asserts.push_back(it);
    }

  vector<SSA_step_reft> assert_vec (asserts.begin(), asserts.end());

    vector<SSA_step_reft>::iterator it;
    //sort(assert_vec.begin(), assert_vec.end(), compare_asserts);
    for (first_it = asserts.begin(); first_it != asserts.end(); first_it++)
    {
      //for (second_it = first_it; second_it != asserts.end(); second_it++)
      //{
        //if (distance(first_it, second_it) > 0)
        {
          if (first_it != second_it)
          {
            if (assert_deps[first_it->first][second_it->first] == DEPT)
            {
              if (check_implication(first_it->first, second_it->first) == true)
              {
                assert_imps[first_it->first][second_it->first] = IMP;
                if (mustprint)
                {
                  std::cout << "Adding the assertion implication (" <<
                  from_expr(ns, "", first_it->first->cond_expr) << " => " <<
                  from_expr(ns, "", second_it->first->cond_expr) << ")" << std::endl;
                }
              }
            }
          }
        }
      //}
    }

    std::cout << "Printing assertion implications:" << std::endl;
    for (map<SSA_step_reft,map<SSA_step_reft,bool> >::iterator dep_first_it = assert_imps.begin(); dep_first_it != assert_imps.end(); ++dep_first_it)
      for (map<SSA_step_reft,bool>::iterator dep_second_it = dep_first_it->second.begin(); dep_second_it != dep_first_it->second.end(); ++dep_second_it)
      std::cout << "(" << from_expr(ns, "", dep_first_it->first->cond_expr) << " => " << from_expr(ns, "", dep_second_it->first->cond_expr) << ")" << std::endl;

}
 */
