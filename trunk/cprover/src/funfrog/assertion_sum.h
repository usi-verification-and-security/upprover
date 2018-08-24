/*******************************************************************
 Module: Propositional encoding of an SSA-form,
         And checking of its satisfiability

 Author: Ondrej Sery

 \*******************************************************************/

#ifndef CPROVER_PROP_ASSERTION_SUM_H
#define CPROVER_PROP_ASSERTION_SUM_H

#include <util/ui_message.h>

class summarization_contextt;

class assertion_sumt:public messaget       //This class is deletable
{
public:
    assertion_sumt(
          summarization_contextt& _summarization_context,
          ui_message_handlert &_message_handler,
          unsigned long &_max_memory_used
          ) :
          summarization_context(_summarization_context),
          message_handler (_message_handler),
          max_memory_used(_max_memory_used)
          {set_message_handler(_message_handler);};
          
    virtual ~assertion_sumt() {}

protected:
  // Summarizing context (summary_store needed)
  summarization_contextt& summarization_context;

  ui_message_handlert &message_handler;

  unsigned long &max_memory_used;

};
#endif
