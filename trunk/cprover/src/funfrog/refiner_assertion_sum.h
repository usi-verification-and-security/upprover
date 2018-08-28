/*******************************************************************
 Module: Refining schema for function summarization.
         Supposed to have different implementations.

 Author: Grigory Fedyukovich

 \*******************************************************************/

#ifndef CPROVER_REFINER_ASSERTION_SUM_H
#define CPROVER_REFINER_ASSERTION_SUM_H

#include <util/message.h>

class summary_storet;
class subst_scenariot;
class call_tree_nodet;
class check_opensmt2t;
class partitioning_target_equationt;

enum class refinement_modet{
    FORCE_INLINING,
    RANDOM_SUBSTITUTION,
    SLICING_RESULT
    // anything else?
};

class refiner_assertion_sumt:public messaget
{
public:
  refiner_assertion_sumt(
          summary_storet & summary_store,
          subst_scenariot &_omega,
          refinement_modet _mode,
          message_handlert &_message_handler,
          const unsigned _last_assertion_loc
          ) :
          summary_store(summary_store),
          omega(_omega),
          mode(_mode),
          //out(_out),
          message_handler(_message_handler),
          last_assertion_loc(_last_assertion_loc)
          {set_message_handler(_message_handler);};

  const std::list<call_tree_nodet*>& get_refined_functions() const { return refined_functions; }
  void set_refine_mode(refinement_modet _mode){ mode = _mode; }

  void mark_sum_for_refine(const check_opensmt2t &decider, call_tree_nodet &summary,
                             partitioning_target_equationt &equation);

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

  std::list<call_tree_nodet*> refined_functions;

  void reset_inline(call_tree_nodet& summary);
  void reset_random(call_tree_nodet& summary);


    void reset_depend(const check_opensmt2t &decider, call_tree_nodet& summary, partitioning_target_equationt &equation);

  void set_inline_sum(call_tree_nodet& summary);
};

#endif
