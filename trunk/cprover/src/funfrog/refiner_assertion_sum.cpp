/*******************************************************************

 Module: Refining schema for function summarization.
         Supposed to have different implementations.

 Author: Grigory Fedyukovich

\*******************************************************************/


#include <stdlib.h>
#include "refiner_assertion_sum.h"

// #define DEBUG_REFINER

/*******************************************************************

 Function: refiner_assertion_sumt::refine

 Inputs:

 Outputs:

 Purpose: Analyses the results of slicing in order to refine,
          Which function call to inline, which to summarize and which to havoc

\*******************************************************************/

void refiner_assertion_sumt::refine(prop_convt& decider)
{
  refined_functions.clear();
  switch (mode){
    case FORCE_INLINING:
      reset_inline();
      break;
    case RANDOM_SUBSTITUTION:
      reset_random();
      break;
    case SLICING_RESULT:
      reset_depend(decider);
      break;
    default:
      assert(false);
      break;
  }
}

void refiner_assertion_sumt::set_inline_sum(int i)
{
  out << "*** REFINING function: " << (*summs[i]).get_summary_info().get_function_id() << std::endl;
  (*summs[i]).set_inline();
  refined_functions.push_back(&(*summs[i]).get_summary_info());
}

void refiner_assertion_sumt::reset_inline()
{
  for (unsigned i = 0; i < summs.size(); i++){
    if ((*summs[i]).get_precision() != INLINE){
      set_inline_sum(i);
    }
  }
}

void refiner_assertion_sumt::reset_random()
{
  unsigned summs_size = 0;
  //unsigned havoc_size = 0;       // maybe, it will be useful
  for (unsigned i = 0; i < summs.size(); i++){
    summary_precisiont precision = (*summs[i]).get_precision();
    if (precision == SUMMARY){
      summs_size++;
    }/* else if (precision == NONDET){
      havoc_size++;
    }*/
  }

  unsigned reset_size = 0;

  while (reset_size == 0){
    // just in case if random function returns false for every function call
    for (unsigned i = 0; i < summs.size(); i++){
      summary_precisiont precision = (*summs[i]).get_precision();
      if ((precision == SUMMARY) ||    // if there were some summaries,
                                       // try to inline them first
          (precision == NONDET && summs_size == 0)){ // and if there were not
                                                     // then refine havoced calls
        if (rand() % 1000 < 300 || rand() % 1000 > 800){
          set_inline_sum(i);
          reset_size++;
        }
      }                                // TODO: we can actually try do it vice-versa
    }                                  // but due to more sophisticated choice of nondets in s_info init
  }                                    // there are more chances that the reason of SAT was in 2weak summaries
}

void refiner_assertion_sumt::reset_depend(prop_convt& decider, bool do_callstart)
{
  std::vector<irep_idt> tmp;

  partitionst& parts = equation.get_partitions();
  for (unsigned i = 0; i < parts.size(); i++) {
    partitiont part = parts[i];
    if (!part.ignore && part.is_summary) {
      partition_ifacet ipart = part.get_iface();
#     ifdef DEBUG_REFINER
      out<< "*** checking " << ipart.function_id << ":" << std::endl;
#     endif
      if (part.applicable_summaries.empty()) {
#       ifdef DEBUG_REFINER
        out<< "    -- no applicable summaries" << std::endl;
#       endif
        tmp.push_back(ipart.function_id);
      }
      if (decider.prop.l_get(ipart.callstart_literal).is_true()){
#       ifdef DEBUG_REFINER
        out<< "    -- callstart literal is true" << std::endl;
#       endif
        if (do_callstart){
          tmp.push_back(ipart.function_id);
        }
      }
    }
  }

  if (tmp.size() == 0) {
    // NOTE: If there is no bug in FunFrog ;-), this means that the assertion 
    // violation is real!
    assert(false);
    out << "Checking of the error trace didn't detect any dependencies." << std::endl
                  << "Try random for this iteration." << std::endl;
    reset_random();
  } else {
    // inline all calls without applicable summaries
    for (unsigned i = 0; i < summs.size(); i++){
      if ((*summs[i]).get_precision() != INLINE){
        for (unsigned j = 0; j < tmp.size(); j++){
          if (tmp[j] == (*summs[i]).get_summary_info().get_function_id()){
            set_inline_sum(i);
            break;
          }
        }
      }
    }
  }
  tmp.clear();
}
