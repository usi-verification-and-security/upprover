/*******************************************************************

 Module: Refining schema for function summarization.
         Supposed to have different implementations.

 Author: Grigory Fedyukovich

\*******************************************************************/

#include "refiner_assertion_sum.h"

/*******************************************************************

 Function: refiner_assertion_sumt::refine

 Inputs:

 Outputs:

 Purpose: Analyses the results of slicing in order to refine,
          Which function call to inline, and which to summararize

\*******************************************************************/

bool refiner_assertion_sumt::refine()
{
/*   if (summarization_context.enable_refinement){
    if (!equation.any_applicable_summaries() ){
      out << "Function summaries neither valid for current goal nor exist. Continuing inlining everything.\n";
      summarization_context.enable_refinement = false;
      summarization_context.force_inlining = true;
      return true;
    }
  }*/

  if (!summarization_context.enable_refinement){             // after unsuccessful attempt of substituting summaries
    summarization_context.enable_refinement = true;          // try inlining everything at next step
  } else {
    summarization_context.enable_refinement = false;       // after unsuccessful attempt
    summarization_context.force_inlining = true;           // try inlining everything at next step
  }
  return false;

}
