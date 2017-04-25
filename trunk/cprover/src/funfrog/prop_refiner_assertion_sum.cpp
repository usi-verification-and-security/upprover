/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

/* 
 * File:   prop_refiner_assertion_sumt.cpp
 * Author: karinek
 * 
 * Created on 09 January 2017, 20:01
 */

#include "prop_refiner_assertion_sum.h"


/*******************************************************************

 Function: refiner_assertion_sumt::refine

 Inputs:

 Outputs:

 Purpose: Analyses the results of slicing in order to refine,
          Which function call to inline, which to summarize and which to havoc

\*******************************************************************/
void prop_refiner_assertion_sumt::refine(
        const prop_conv_solvert &decider, 
        summary_infot& summary, 
        prop_partitioning_target_equationt &equation)
{
  refined_functions.clear();
  switch (mode){
    case FORCE_INLINING:
      reset_inline(summary);
      break;
    case RANDOM_SUBSTITUTION:
      reset_random(summary);
      break;
    case SLICING_RESULT:
      reset_depend(decider, summary, equation);
      break;
    default:
      assert(false);
      break;
  }
}

void prop_refiner_assertion_sumt::reset_depend(
        const prop_conv_solvert &decider, 
        summary_infot& summary, 
        prop_partitioning_target_equationt &equation)
{
  std::vector<summary_infot*> tmp;

  partitionst& parts = equation.get_partitions();
  for (unsigned i = 0; i < parts.size(); i++) {
    partitiont part = parts[i];
    if (!part.ignore && (part.summary || part.stub)) {
      partition_ifacet ipart = part.get_iface();
#     ifdef DEBUG_REFINER
      std::cout<< "*** checking " << ipart.function_id << ":" << std::endl;
#     endif
      /*if (part.summary && part.applicable_summaries.empty()) {
#       ifdef DEBUG_REFINER
        std::cout<< "    -- no applicable summaries" << std::endl;
#       endif
        tmp.push_back(&ipart.summary_info);
      }*/
      if (decider.l_get(ipart.callstart_literal).is_true()){ // in the variant will do prop.lget
#       ifdef DEBUG_REFINER
        std::cout<< "    -- callstart literal is true" << std::endl;
#       endif
        if (ipart.summary_info.get_precision() != INLINE){
          if (ipart.summary_info.is_recursion_nondet()){
              status() << "Automatically increasing unwinding bound for " << ipart.summary_info.get_function_id() << eom;
              omega.refine_recursion_call(ipart.summary_info);
          }
          set_inline_sum(ipart.summary_info);
        }
      }
    }
  }
}
