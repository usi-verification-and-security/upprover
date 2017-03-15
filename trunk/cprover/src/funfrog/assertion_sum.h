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

#include "assertion_info.h"
#include "summarization_context.h"
#include "partitioning_target_equation.h"

extern time_periodt global_satsolver_time;
extern time_periodt global_sat_conversion_time;

class assertion_sumt:public messaget
{
public:
    assertion_sumt(
          summarization_contextt& _summarization_context,
          //std::ostream &_out,
          ui_message_handlert &_message_handler,
          unsigned long &_max_memory_used
          ) :
          summarization_context(_summarization_context),
          solving_time(0),
          //out(_out),
          message_handler (_message_handler),
          max_memory_used(_max_memory_used)
          {set_message_handler(_message_handler);};
          
    virtual ~assertion_sumt() {}

    const fine_timet& get_solving_time() { return solving_time; };

protected:
  // Summarizing context (summary_store needed)
  summarization_contextt& summarization_context;

  // SAT solving time
  time_periodt solving_time;

  //std::ostream &out;
  ui_message_handlert &message_handler;

  unsigned long &max_memory_used;

};
#endif