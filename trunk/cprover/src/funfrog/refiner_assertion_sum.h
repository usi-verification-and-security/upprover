/*******************************************************************
 Module: Refining schema for function summarization.
         Supposed to have different implementations.

 Author: Grigory Fedyukovich

 \*******************************************************************/

#ifndef CPROVER_REFINER_ASSERTION_SUM_H
#define CPROVER_REFINER_ASSERTION_SUM_H

#include <util/message.h>
#include "summarization_context_fwd.h"

class summary_storet;
class subst_scenariot;
class call_tree_nodet;

class refiner_assertion_sumt:public messaget
{
public:
  refiner_assertion_sumt(
          summary_storet & summary_store,
          subst_scenariot &_omega,
          refinement_modet _mode,
          message_handlert &_message_handler,
          const unsigned _last_assertion_loc,
          bool _valid
          ) :
          summary_store(summary_store),
          omega(_omega),
          mode(_mode),
          //out(_out),
          message_handler(_message_handler),
          last_assertion_loc(_last_assertion_loc),
          valid (_valid)
          {set_message_handler(_message_handler);};

  std::list<call_tree_nodet*>& get_refined_functions(){ return refined_functions; }
  void set_refine_mode(refinement_modet _mode){ mode = _mode; }

protected:
  summary_storet & summary_store;
  // substituting scenario
  subst_scenariot &omega;

  // Mode of refinement
  refinement_modet mode;

  // Default output
  //std::ostream &out;
  message_handlert &message_handler;

  // Location of the last assertion to be checked
  const unsigned last_assertion_loc;

  // Mode of changing the summaries validity
  bool valid;

  std::list<call_tree_nodet*> refined_functions;

  void reset_inline(call_tree_nodet& summary);
  void reset_random(call_tree_nodet& summary);

  // not in use now
  void reset_depend_rec(std::vector<call_tree_nodet*>& dep, call_tree_nodet& summary);

  void set_inline_sum(call_tree_nodet& summary);
};

#endif
