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
  switch (mode){
    case FORCE_INLINING:
      reset_inline();
      break;
    case RANDOM_SUBSTITUTION:
      reset_random();
      break;
    case SLICING_RESULT:
      // TODO: strengthen the analysis. for the moment, refinement loop in this mode may not terminate
      reset_depend();
      break;
    default:
      assert(false);
      break;
  }
}

void refiner_assertion_sumt::reset_inline()
{
  for (unsigned i = 0; i < summs.size(); i++){
    if ((*summs[i]).get_precision() != INLINE){
      out << "*** REFINING function: " << (*summs[i]).get_summary_info().get_function_id() << std::endl;
      (*summs[i]).set_inline();
      refined_functions.push_back(&(*summs[i]).get_summary_info());
    }
  }
}

void refiner_assertion_sumt::reset_random()
{
  for (unsigned i = 0; i < summs.size(); i++){
    if ((*summs[i]).get_precision() == SUMMARY){
      if (rand() % 1000 < 300 || rand() % 1000 > 800){
        out << "*** REFINING function: " << (*summs[i]).get_summary_info().get_function_id() << std::endl;
        (*summs[i]).set_inline();
        refined_functions.push_back(&(*summs[i]).get_summary_info());
      }
    }
  }
}

void refiner_assertion_sumt::reset_depend()
{
  for (unsigned i = 0; i < summs.size(); i++){
    if ((*summs[i]).get_precision() != INLINE){
      if (true){ // TODO: (!any_applicable(functions, (*summs[i]).get_summary_info().get_function_id(), false)){
        (*summs[i]).set_inline();
        out << "*** REFINING function: " << (*summs[i]).get_summary_info().get_function_id() << std::endl;
        refined_functions.push_back(&(*summs[i]).get_summary_info());
      }
    }
  }
}
