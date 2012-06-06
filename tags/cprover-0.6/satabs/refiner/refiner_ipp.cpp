/*******************************************************************\
  
Module: Predicate Refinement for CEGAR

Author: Daniel Kroening

Date: September 2005
 
\*******************************************************************/

#include <assert.h>
#include <iostream>

#include "refiner_ipp.h"
#include "../abstractor/discover_predicates.h"
#include "../abstractor/canonicalize.h"
#include "../simulator/simulator_ipp.h"

//#define DEBUG

/*******************************************************************\

Function: refiner_ippt::refine_prefix

  Inputs:

 Outputs:

 Purpose: generate a new set of predicates given a spurious counterexample

\*******************************************************************/

bool refiner_ippt::refine_prefix(
  predicatest &predicates, 
  abstract_modelt &abstract_model,
  const fail_infot &fail_info)
{
  status("Refining set of predicates according to counterexample");

  concrete_counterexamplet tmp_concrete_counterexample;
  fail_infot tmp_fail_info;

  simulator_ippt simulator_ipp(
    argst(*message_handler, ns, concrete_model),
    limit);
    
  abstract_counterexamplet tmp_abstract_counterexample;
  
  tmp_abstract_counterexample.steps=fail_info.all_steps;

  // undo slicing  
  for(abstract_counterexamplet::stepst::iterator 
      c_it=tmp_abstract_counterexample.steps.begin();
      c_it!=tmp_abstract_counterexample.steps.end();
      c_it++)
    c_it->relevant=true;

  if(!simulator_ipp.check_prefix(
    predicates,
    abstract_model,
    tmp_abstract_counterexample,
    tmp_concrete_counterexample,
    tmp_fail_info))
    throw "IPP refiner thinks counterexample is not spurious";
  
  // predicates from interpolants
  
  const expr_listt &interpolant_list=
    simulator_ipp.interpolant_list;
    
  assert(interpolant_list.size()==
         tmp_abstract_counterexample.steps.size()-1);
  
  bool found_new=false;

  {
    expr_listt::const_iterator
      i_it=interpolant_list.begin();
    
    for(abstract_counterexamplet::stepst::const_iterator 
        c_it=fail_info.all_steps.begin();
        c_it!=fail_info.all_steps.end();
        i_it++, c_it++)
    {
      // don't do last step -- it's the assertion
      if(c_it==--fail_info.all_steps.end()) break;
    
      assert(i_it!=interpolant_list.end());

      abstract_counterexamplet::stepst::const_iterator 
        next_c_it=c_it;

      next_c_it++;
      
      add_predicates(c_it->pc,
                     predicates, *i_it, found_new, TO);
                     
      add_predicates(next_c_it->pc,
                     predicates, *i_it, found_new, FROM);
    }
  }

  return !found_new;
}
