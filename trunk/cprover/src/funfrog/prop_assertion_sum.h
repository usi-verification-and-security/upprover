/*******************************************************************
 Module: Propositional encoding of an SSA-form,
         And checking of its satisfiability

 Author: Ondrej Sery

 \*******************************************************************/

#ifndef CPROVER_PROP_ASSERTION_SUM_H
#define CPROVER_PROP_ASSERTION_SUM_H

#include <namespace.h>
#include <ui_message.h>
#include <time_stopping.h>
#include <fstream>
#include <util/threeval.h>
#include "solvers/smtcheck_opensmt2.h"

#include "assertion_info.h"
#include "summarization_context.h"
#include "partitioning_target_equation.h"

extern fine_timet global_satsolver_time;
extern fine_timet global_sat_conversion_time;

class prop_assertion_sumt:public messaget
{
public:
  prop_assertion_sumt(
          summarization_contextt& _summarization_context,
          partitioning_target_equationt &_target,
          //std::ostream &_out,
          ui_message_handlert &_message_handler,
          unsigned long &_max_memory_used
          ) :
          summarization_context(_summarization_context),
          equation(_target),
          solving_time(0),
          //out(_out),
          message_handler (_message_handler),
          max_memory_used(_max_memory_used)
          {set_message_handler(_message_handler);};

  bool assertion_holds(const assertion_infot &assertion, const namespacet &ns, smtcheck_opensmt2t& decider, interpolating_solvert& interpolator);

  const fine_timet& get_solving_time() { return solving_time; };

  void error_trace(smtcheck_opensmt2t& decider, const namespacet &ns);

private:
  // Summarizing context (summary_store needed)
  summarization_contextt& summarization_context;

  // Store for the symex result
  partitioning_target_equationt &equation;

  // SAT solving time
  fine_timet solving_time;

  //std::ostream &out;
  ui_message_handlert &message_handler;

  unsigned long &max_memory_used;

  bool is_satisfiable(smtcheck_opensmt2t& decider);

};
#endif
