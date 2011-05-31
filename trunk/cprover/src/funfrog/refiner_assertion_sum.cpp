/*******************************************************************

 Module: Refining schema for function summarization.
         Supposed to have different implementations.

 Author: Grigory Fedyukovich

\*******************************************************************/


#include <stdlib.h>
#include "refiner_assertion_sum.h"

/*******************************************************************

 Function: refiner_assertion_sumt::refine

 Inputs:

 Outputs:

 Purpose: Analyses the results of slicing in order to refine,
          Which function call to inline, which to summarize and which to havoc

\*******************************************************************/

void refiner_assertion_sumt::refine()
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
      reset_depend();
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
  for (unsigned i = 0; i < summs.size(); i++){
    if ((*summs[i]).get_precision() != INLINE){
      if (rand() % 1000 < 300 || rand() % 1000 > 800){
        set_inline_sum(i);
      }
    }
  }
}

void refiner_assertion_sumt::reset_depend()
{
  std::vector<irep_idt*> tmp;
  partitionst& parts = equation.get_partitions();
  for (unsigned i = 0; i < parts.size(); i++) {
    if (parts[i].applicable_summaries.empty()) {
      tmp.push_back(&parts[i].get_iface().function_id);
    }
  }

  if (tmp.size() == 0) {
    // all summaries are applicable. try randomization then
    reset_random();
  } else {
    // inline all calls without applicable summaries
    for (unsigned i = 0; i < summs.size(); i++){
      if ((*summs[i]).get_precision() != INLINE){
        for (unsigned j = 0; j < tmp.size(); j++){
          if ((*tmp[j]) == (*summs[i]).get_summary_info().get_function_id()){
            set_inline_sum(i);
            break;
          }
        }
      }
    }
  }
  mode = RANDOM_SUBSTITUTION;
}
