/*******************************************************************
 Module: Refining schema for function summarization.
         Supposed to have different implementations.

 Author: Grigory Fedyukovich

 \*******************************************************************/

#ifndef CPROVER_REFINER_ASSERTION_SUM_H
#define CPROVER_REFINER_ASSERTION_SUM_H

#include "assertion_info.h"
#include "summarization_context.h"
#include "partitioning_target_equation.h"

class refiner_assertion_sumt
{
public:
  refiner_assertion_sumt(
          summarization_contextt &_summarization_context,
          partitioning_target_equationt &_target,
          std::ostream &_out
          ) :
          summarization_context(_summarization_context),
          equation(_target),
          out(_out)
          {};

  bool refine();

private:

  // Shared information about the program and summaries to be used during
  // analysis
  summarization_contextt &summarization_context;

  // Store for the symex result
  partitioning_target_equationt &equation;

  std::ostream &out;

};
#endif
