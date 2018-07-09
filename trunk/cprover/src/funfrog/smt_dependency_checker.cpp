/* 
 * File:   smt_dependency_checkert.cpp
 * Author: karinek
 * 
 * Created on 09 January 2017, 15:13
 */

#include "smt_dependency_checker.h"
#include "utils/naming_helpers.h"
#include "solvers/smtcheck_opensmt2_lra.h"

std::pair<bool, fine_timet> smt_dependency_checkert::check_implication(SSA_step_reft &c1, SSA_step_reft &c2)
{
  try{
  smtcheck_opensmt2t* decider = new smtcheck_opensmt2t_lra(0, "implication checker", false);
  decider->new_partition();

  convert_delta_SSA(*decider, c1, c2);

  if (VERBOSE) status() << ("RESULT");
  time_periodt duration;
  absolute_timet initial, end;
  initial=current_time();
  bool r = decider->solve();
  end=current_time();
  duration = end - initial;

  status() << "SOLVER TIME FOR check_implication: " << duration << eom;
  // solve it
  return std::make_pair(!r, duration);
  
  } catch (const std::bad_alloc &e)
  {
    error ()  << "smth is wrong: " << e.what()  << eom;
    return std::make_pair(true, (fine_timet)0);
  }
  catch (const char* e)
  {
    error () << "\nCaught exception: " << e << eom;
    return std::make_pair(true, (fine_timet)0);
  }
  catch (const std::string &s)
  {
    error () << "\nCaught exception: " << s << eom;
    return std::make_pair(true, (fine_timet)0);
  }
}

long smt_dependency_checkert::find_implications()
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
//  vector<bool> stronger(asserts.size(), false);
  std::vector<bool> weaker(asserts.size(), false);
  
    /*
    cout << "Printing assertions before ordering." << std::endl;
    for (it = asserts.begin(); it != asserts.end(); it++)
    {
    	cout << from_expr(ns, "", (*it)->cond_expr) << std::endl;
    }
    */

    //sort(asserts.begin(), asserts.end(), compare_asserts);

    /*
    cout << "Printing assertions after ordering." << std::endl;
    for (it = asserts.begin(); it != asserts.end(); it++)
    {
    	cout << from_expr(ns, "", (*it)->cond_expr) << std::endl;
    }
    */

  std::ofstream hl_may_impl;
  hl_may_impl.open ("__hl_may_impl");

  for (unsigned i = 0; i < asserts.size(); i++)
  {
    SSA_step_reft& assert_1 = asserts[i];
    //unsigned int lstart = IMAX(0, i - (treshold - 1));
	  //unsigned int lend = IMIN(i + (treshold), asserts.size());
    for (unsigned j = i+1; j < asserts.size(); j++)
    {
      checks++;
      std::pair<bool, fine_timet> checkres;
      SSA_step_reft& assert_2 = asserts[j];
      if (compare_assertions(assert_1, assert_2)
          && assert_deps[assert_1][assert_2] == DEPT
          )
      {
        impchecks++;
        if (VERBOSE)
        {
          status () << "Comparing the assertions " <<
            from_expr(ns, "", (*assert_1)->cond_expr) << " and " <<
            from_expr(ns, "", (*assert_2)->cond_expr) << eom;
        }
                checkres = check_implication(assert_1, assert_2);

        if (checkres.first == true)
        {
          true_time = true_time + checkres.second.get_t();
          if (VERBOSE) {status () << "check_implication returned TRUE" << eom;}
          if (checkres.second.get_t() <= impl_timeout)
          {
            assert_imps[assert_1][assert_2] = IMP;
//            if (VERBOSE)
//            {
//              std::cout << "Adding the assertion implication \n (" <<
//                from_expr(ns, "", (*assert_1)->cond_expr) << ") [" << (*assert_1)->source.pc->location.get_line() << "] [stronger] \n => \n (" <<
//                from_expr(ns, "", (*assert_2)->cond_expr) << ") [" << (*assert_2)->source.pc->location.get_line() << "] [weaker]" << std::endl;
//            }

            weaker[j] = true;
//            stronger[j] = true;
            hl_may_impl << (*assert_1)->source.pc->source_location.get_property_id() << " " <<
                (*assert_2)->source.pc->source_location.get_property_id() << " " <<
                distance(SSA_steps.begin(), assert_1) << " " <<
                distance(SSA_steps.begin(), assert_2) << std::endl;

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
//    for (map<SSA_step_reft,map<SSA_step_reft,bool> >::iterator dep_first_it = assert_imps.begin(); dep_first_it != assert_imps.end(); ++dep_first_it)
//      for (map<SSA_step_reft,bool>::iterator dep_second_it = dep_first_it->second.begin(); dep_second_it != dep_first_it->second.end(); ++dep_second_it)
//      std::cout << "(" << from_expr(ns, "", dep_first_it->first->cond_expr) << " => " << from_expr(ns, "", dep_second_it->first->cond_expr) << ")" << std::endl;

  hl_may_impl.close();

//  cout << "Discarded assertions: " << discarded << std::endl;
  if (notdisc > 0) std::cout << "WARNING: " << notdisc << " true implications exceeded timeout!" << std::endl;

//  cout << "Total number of implication checks: " << impchecks << std::endl;
//  cout << "Total number of comparisons: " << checks << std::endl;

  for (int i = asserts.size() - 1; i >= 0; i--)
  //for (unsigned i = 0; i < asserts.size(); i++)
  {
    if (weaker[i] == true)
	  {
		  SSA_step_reft& removable = asserts[i];
      warning () << "\nRedundant assertion at:\n" <<
	  "  file \"" << (*removable)->source.pc->source_location.get_file() <<
	  "\",\n  function \"" << (*removable)->source.pc->source_location.get_function() <<
	  "\",\n  line " << (*removable)->source.pc->source_location.get_line() << ":\n  " <<
          from_expr(ns, "", (*removable)->source.pc->guard) << "\n" << eom;


      (*removable)->ignore = true;
	}
  }
//  try{
//    ofstream hl_stronger;
//    ofstream hl_weaker;
//    hl_stronger.open ("__hl_stronger");
//    hl_weaker.open ("__hl_weaker");
//    for (int i = asserts.size() - 1; i >= 0; i--){
//      SSA_step_reft& ass = asserts[i];
//      if (weaker[i] == true)
//        hl_weaker << (*ass)->source.pc->location.get_claim().c_str() << std::endl;
//      if (stronger[i] == true)
//        hl_stronger << (*ass)->source.pc->location.get_claim().c_str() << std::endl;
//    }
//
//    hl_stronger.close();
//    hl_weaker.close();
//  }  catch (const bad_alloc &e)
//  {
//    cout  << "smth is very wrong: " << e.what()  << std::endl;
//
//  }
  return to_time;

}

void smt_dependency_checkert::convert_delta_SSA(smtcheck_opensmt2t &decider,
    SSA_step_reft &it1, SSA_step_reft &it2)
{
  convert_guards(decider, it1, it2);
  convert_assignments(decider, it1, it2);
  convert_assumptions(decider, it1, it2);
  convert_assertions(decider, it2);
  convert_io(decider, it1, it2);
}

void smt_dependency_checkert::deep_convert_guards(smtcheck_opensmt2t &decider, exprt exp){
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

void smt_dependency_checkert::set_guards_to_true(smtcheck_opensmt2t &decider, exprt exp){
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

void smt_dependency_checkert::convert_assignments(
    smtcheck_opensmt2t &decider, SSA_step_reft &it1, SSA_step_reft &it2)
{
  SSA_step_reft it=it1;
  while(it!=it2){
    it++;

    if((*it)->is_assignment() && !(*it)->ignore)
    {
      //std::cout << "convert assign :" << from_expr(ns, "", (*it)->cond_expr) <<"\n";
      decider.set_to_true((*it)->cond_expr);
    }
  }
}

void smt_dependency_checkert::convert_guards(
  smtcheck_opensmt2t &decider, SSA_step_reft &it1, SSA_step_reft &it2)
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
        decider.convert((*it)->cond_expr);
        //deep_convert_guards(decider, ((*it)->cond_expr));
      }
    it++;
  }
}

void smt_dependency_checkert::convert_assumptions(
  smtcheck_opensmt2t &decider, SSA_step_reft &it1, SSA_step_reft &it2)
{
  SSA_step_reft it=it1;
  while(it!=it2)
  {
    if(((*it)->is_assume() || ((*it)->is_assert() && it != it2)) && !(*it)->ignore)
    {
       //std::cout << "convert assume :" << from_expr(ns, "", (*it)->cond_expr) <<"\n";
       decider.set_to_true((*it)->cond_expr);
       set_guards_to_true(decider, ((*it)->cond_expr));
    }
    it++;
  }
}

void smt_dependency_checkert::convert_assertions(
  smtcheck_opensmt2t &decider, SSA_step_reft &it2)
{
  assert((*it2)->is_assert());
  //std::cout << "convert assert :" << from_expr(ns, "", (*it2)->cond_expr) <<"\n";
  set_guards_to_true(decider, ((*it2)->cond_expr));
  decider.set_to_false((*it2)->cond_expr);
}

void smt_dependency_checkert::convert_io(
    smtcheck_opensmt2t &decider, SSA_step_reft &it1, SSA_step_reft &it2)
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
          symbol.set_identifier(CProverStringConstants::IO_CONST + std::to_string(io_count++));
          decider.set_to_true(equal_exprt(tmp, symbol));
          (*it)->converted_io_args.push_back(symbol);
        }
      }
    it++;
  }
}
