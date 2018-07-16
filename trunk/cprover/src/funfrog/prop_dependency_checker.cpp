/* 
 * File:   prop_dependency_checkert.cpp
 * Author: karinek
 * 
 * Created on 09 January 2017, 15:13
 * 
 */

#include "prop_dependency_checker.h"
#include "utils/naming_helpers.h"
#include <solvers/flattening/bv_pointers.h>
#include "solvers/satcheck_opensmt2.h"

#define VERBOSE false

std::pair<bool, fine_timet> prop_dependency_checkert::check_implication(SSA_steps_it c1, SSA_steps_it c2)
{
  try{

  std::unique_ptr<prop_conv_solvert> decider;
  satcheck_opensmt2t* opensmt = new satcheck_opensmt2t("prop dependency checker");
  opensmt->new_partition();
  bv_pointerst *deciderp = new bv_pointerst(ns, *opensmt);
  deciderp->unbounded_array = bv_pointerst::unbounded_arrayt::U_AUTO;
  decider.reset(deciderp);

  convert_delta_SSA(*decider, c1, c2);

  if (VERBOSE) status() << ("RESULT");
  time_periodt duration;
  absolute_timet initial, end;
  initial=current_time();
  decision_proceduret::resultt r = (*decider).dec_solve();
  end=current_time();
  duration = end - initial;
#ifdef USE_PERIPLO
//  // todo
#else
delete opensmt;
#endif

  if (VERBOSE) {status() << ("SOLVER TIME FOR check_implication: ") << duration << eom;}

  // solve it
  switch (r)
  {
    case decision_proceduret::resultt::D_UNSATISFIABLE:
    {
      if (VERBOSE) status() << ("UNSAT - it holds!") << eom;
      return std::make_pair(true, duration);
    }
    case decision_proceduret::resultt::D_SATISFIABLE:
    {
      if (VERBOSE) status() << ("SAT - doesn't hold") << eom;
      return std::make_pair(false, duration);
    }

    default:
      throw "unexpected result from dec_solve()";
  }
  } catch (const std::bad_alloc &e)
  {
    error()  << "smth is wrong: " << e.what()  << eom;
    return std::make_pair(true, fine_timet(0));
  }
  catch (const char* e)
  {
    error() << "\nCaught exception: " << e << eom;
    return std::make_pair(true, fine_timet(0));
  }
  catch (const std::string &s)
  {
    error() << "\nCaught exception: " << s << eom;
    return std::make_pair(true, fine_timet(0));
  }
}

long prop_dependency_checkert::find_implications()
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
      std::pair<bool, fine_timet> checkres;
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
            from_expr(ns, "", assert_1->cond_expr) << " and " <<
            from_expr(ns, "", assert_2->cond_expr) << eom;
        }
                checkres = check_implication(SSA_steps.begin() + assert1_idx, SSA_steps.begin() + assert2_idx);

        if (checkres.first == true)
        {
          true_time = true_time + checkres.second.get_t();
          if (VERBOSE) {std::cout << "check_implication returned TRUE" << std::endl;}
          if (checkres.second.get_t() <= impl_timeout)
          {
            assert_imps[assert1_idx][assert2_idx] = IMP;
            if (VERBOSE)
            {
              status() << "Adding the assertion implication \n (" <<
                from_expr(ns, "", assert_1->cond_expr) << ") [" << assert_1->source.pc->source_location.get_line() << "] [stronger] \n => \n (" <<
                from_expr(ns, "", assert_2->cond_expr) << ") [" << assert_2->source.pc->source_location.get_line() << "] [weaker]" << eom;
            }

            weaker[i] = false;
            stronger[j] = false;
            hl_may_impl << assert_1->source.pc->source_location.get_property_id() << " " <<
                assert_2->source.pc->source_location.get_property_id() << " " <<
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
        	false_time = false_time + checkres.second.get_t();
        	if (VERBOSE) { status () << "check_implication returned FALSE" << eom;}
        }
        if (checkres.second.get_t() > impl_timeout)
        {
        	long exceeding = checkres.second.get_t() - impl_timeout;
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
  //for (unsigned i = 0; i < asserts.size(); i++)
  {
    if (weaker[i] == true)
	  {
		  auto removable = SSA_steps[asserts[i]];
		  status () << "Removing << " << removable->source.pc->source_location.get_line() << eom;
		  removable->ignore = true;
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
        hl_weaker << ass->source.pc->source_location.get_property_id().c_str() << std::endl;
      if (stronger[i] == true)
        hl_stronger << ass->source.pc->source_location.get_property_id().c_str() << std::endl;
    }

    hl_stronger.close();
    hl_weaker.close();
  }  catch (const std::bad_alloc &e)
  {
    error()  << "smth is very wrong: " << e.what()  << eom;

  }
  return to_time;

}

void prop_dependency_checkert::convert_delta_SSA(prop_conv_solvert &decider,
    SSA_steps_it &it1, SSA_steps_it &it2)
{
  convert_guards(decider, it1, it2);
  convert_assignments(decider, it1, it2);
  convert_assumptions(decider, it1, it2);
  convert_assertions(decider, it2);
  convert_io(decider, it1, it2);
}

void prop_dependency_checkert::deep_convert_guards(prop_conv_solvert &decider, exprt exp){
  if (exp.has_operands())
  {
    for (unsigned i = 0; i < exp.operands().size(); i++){
      deep_convert_guards(decider, exp.operands()[i] );
    }
  } else {
    // TODO: find a more clever way of identifying guards
    if ((from_expr(ns, "", exp)).find("guard") == 1){
      //std::cout << " -> converting " << from_expr(SSA_map[exp]) << "\n";
      decider.convert(SSA_map[exp]);
    }
  }
}

void prop_dependency_checkert::set_guards_to_true(prop_conv_solvert &decider, exprt exp){
  if (exp.has_operands())
  {
    for (unsigned i = 0; i < exp.operands().size(); i++){
      set_guards_to_true(decider, exp.operands()[i] );
    }
  } else {
    // TODO: find a more clever way of identifying guards
    if ((from_expr(ns, "", exp)).find("guard") == 1){
      //std::cout << " -> set to true " << from_expr(SSA_map[exp]) << "\n";
      decider.set_to_true(SSA_map[exp]);
    }
  }
}

void prop_dependency_checkert::convert_assignments(
    prop_conv_solvert &decider, SSA_steps_it &it1, SSA_steps_it &it2)
{
  SSA_steps_it it=it1;
  while(it!=it2){
    it++;

    if((*it)->is_assignment() && !(*it)->ignore)
    {
      //std::cout << "convert assign :" << from_expr(ns, "", (*it)->cond_expr) <<"\n";
      decider.set_to_true((*it)->cond_expr);
    }
  }
}

void prop_dependency_checkert::convert_guards(
  prop_conv_solvert &decider, SSA_steps_it &it1, SSA_steps_it &it2)
{
  SSA_steps_it it=it1;
  SSA_steps_it it3=it2;
  it3++;

  while(it!=it3){
      if ((*it)->cond_expr.is_nil() || (*it)->ignore){
        (*it)->guard_literal=const_literal(false);
      }
      else {
        //std::cout << "convert guard: " << from_expr(ns, "", (*it)->cond_expr) <<"\n";
        decider.convert((*it)->cond_expr);
        //deep_convert_guards(decider, ((*it)->cond_expr));
      }
    it++;
  }
}

void prop_dependency_checkert::convert_assumptions(
  prop_conv_solvert &decider, SSA_steps_it &it1, SSA_steps_it &it2)
{
  SSA_steps_it it=it1;
  while(it!=it2)
  {
    // KE:  merge dev to master, not sure which line is the correct one
    //if(((*it)->is_assume() || ((*it)->is_assert() && it != it2)) && !(*it)->ignore)
    if(((*it)->is_assume() || ((*it)->is_assert() && it ==it1)) && !(*it)->ignore)  
    {
       //std::cout << "convert assume :" << from_expr(ns, "", (*it)->cond_expr) <<"\n";
       decider.set_to_true((*it)->cond_expr);
       set_guards_to_true(decider, ((*it)->cond_expr));
    }
    it++;
  }
}

void prop_dependency_checkert::convert_assertions(
  prop_conv_solvert &decider, SSA_steps_it &it2)
{
  assert((*it2)->is_assert());
  //std::cout << "convert assert :" << from_expr(ns, "", (*it2)->cond_expr) <<"\n";
  set_guards_to_true(decider, ((*it2)->cond_expr));
  decider.set_to_false((*it2)->cond_expr);
}

void prop_dependency_checkert::convert_io(
    prop_conv_solvert &decider, SSA_steps_it &it1, SSA_steps_it &it2)
{
  unsigned io_count=0;
  SSA_steps_it it=it1;
  SSA_steps_it it3=it2;
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
          symbol.set_identifier( CProverStringConstants::IO_CONST + std::to_string(io_count++));
          decider.set_to(equal_exprt(tmp, symbol), true);
          (*it)->converted_io_args.push_back(symbol);
        }
      }
    it++;
  }
}
