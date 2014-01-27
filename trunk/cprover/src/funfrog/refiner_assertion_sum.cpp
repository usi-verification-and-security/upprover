/*******************************************************************

 Module: Refining schema for function summarization.
         Supposed to have different implementations.

 Author: Grigory Fedyukovich

\*******************************************************************/


#include <stdlib.h>
#include "refiner_assertion_sum.h"

//#define DEBUG_REFINER

/*******************************************************************

 Function: refiner_assertion_sumt::refine

 Inputs:

 Outputs:

 Purpose: Analyses the results of slicing in order to refine,
          Which function call to inline, which to summarize and which to havoc

\*******************************************************************/

void refiner_assertion_sumt::refine(prop_convt& decider, summary_infot& summary)
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
      reset_depend(decider, summary);
      break;
    default:
      assert(false);
      break;
  }
}

void refiner_assertion_sumt::set_inline_sum(summary_infot& summary)
{
  if (summary.get_call_location() <= last_assertion_loc){
    status(std::string("*** REFINING function: ") + summary.get_function_id().c_str());
    summary.set_inline();
    refined_functions.push_back(&summary);
  }
  summarization_context.set_valid_summaries(summary.get_function_id(), valid);
}

void refiner_assertion_sumt::reset_inline(summary_infot& summary)
{
  for (call_sitest::iterator it = summary.get_call_sites().begin();
          it != summary.get_call_sites().end(); ++it)
  {
    if ((it->second).get_precision() != INLINE){
      set_inline_sum(it->second);
    }
    reset_inline(it->second);
  }
}

void refiner_assertion_sumt::reset_random(summary_infot& summary)
{
  unsigned summs_size = omega.get_summaries_count();
    for (call_sitest::iterator it = summary.get_call_sites().begin();
            it != summary.get_call_sites().end(); ++it)
    {
      summary_precisiont precision = (it->second).get_precision();
      if ((precision == SUMMARY) ||    // if there were some summaries,
                                       // try to inline them first
          (precision == HAVOC && summs_size == 0)){  // and if there were not
                                                     // then refine havoced calls
        if (rand() % 1000 < 300 || rand() % 1000 > 800){
          set_inline_sum(it->second);
        }
      }
      reset_random(it->second);
                                       // TODO: we can actually try do it vice-versa
    }                                  // but due to more sophisticated choice of nondets in s_info init
                                       // there are more chances that the reason of SAT was in 2weak summaries
}

void refiner_assertion_sumt::reset_depend(prop_convt& decider, summary_infot& summary)
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
#     ifdef USE_PERIPLO
      if (!decider.prop.l_get(ipart.callstart_literal).is_false()){
#     else
      if (decider.prop.l_get(ipart.callstart_literal).is_true()){
#     endif
#       ifdef DEBUG_REFINER
        std::cout<< "    -- callstart literal is true" << std::endl;
#       endif
        if (ipart.summary_info.get_precision() != INLINE){
          if (ipart.summary_info.is_recursion_nondet()){
              status() << "Automatically increasing unwinding bound for " << ipart.summary_info.get_function_id() << "\n";
              omega.refine_recursion_call(ipart.summary_info);
          }s
          set_inline_sum(ipart.summary_info);
        }
      }
    }
  }

}

// something old
void refiner_assertion_sumt::reset_depend_rec(std::vector<summary_infot*>& dep, summary_infot& summary)
{
  for (call_sitest::iterator it = summary.get_call_sites().begin();
          it != summary.get_call_sites().end(); ++it)
  {
    summary_infot& call = it->second;
    if (call.get_precision() != INLINE){
      for (unsigned j = 0; j < dep.size(); j++){
        if (dep[j] == &call){
          /*if (call.is_unwind_exceeded()){
            std::cout << "The call " << call.get_function_id() << " cannot be refined because the maximum unwinding bound is exceeded\n";
          } else {*/
            if (call.is_recursion_nondet()){
              status() << "Automatically increasing unwinding bound for " << call.get_function_id() << "\n";
              omega.refine_recursion_call(call);
            }
            set_inline_sum(call);
            break;
          //}
        }
      }
    } else {
      reset_depend_rec(dep, call);
    }
  }
}
