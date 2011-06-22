/*******************************************************************
 Module: Refining schema for function summarization.
         Supposed to have different implementations.

 Author: Grigory Fedyukovich

 \*******************************************************************/

#ifndef CPROVER_REFINER_ASSERTION_SUM_H
#define CPROVER_REFINER_ASSERTION_SUM_H

#include "assertion_info.h"
#include "summary_info.h"
#include "summarization_context.h"
#include "partitioning_target_equation.h"

class refiner_assertion_sumt
{
public:
  refiner_assertion_sumt(
          summarization_contextt &_summarization_context,
          std::vector<call_summaryt*>& _summs,
          partitioning_target_equationt &_target,
          refinement_modet _mode,
          std::ostream &_out
          ) :
          summarization_context(_summarization_context),
          summs(_summs),
          equation(_target),
          mode(_mode),
          out(_out)
          {};

  void refine(prop_convt& decider);
  std::list<summary_infot*>& get_refined_functions(){ return refined_functions; }

protected:
  // Shared information about the program and summaries to be used during
  // analysis
  summarization_contextt &summarization_context;

  // Which functions should be summarized, abstracted from, and which inlined
  std::vector<call_summaryt*>& summs;

  // Store for the symex result
  partitioning_target_equationt &equation;

  // Mode of refinement
  refinement_modet mode;

  std::ostream &out;

  std::list<summary_infot*> refined_functions;

  void reset_inline();
  void reset_random();
  void reset_depend(prop_convt& decider, bool do_callstart = true);

  void set_inline_sum(int i);
};

#endif
