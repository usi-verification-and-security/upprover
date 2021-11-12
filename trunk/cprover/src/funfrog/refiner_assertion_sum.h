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
class partitioning_target_equationt;
class solvert;

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

  std::list<call_tree_nodet*>& get_refined_functions() { return refined_functions; }
  void set_refine_mode(refinement_modet _mode){ mode = _mode; }

  void mark_sum_for_refine(const solvert &solvert, call_tree_nodet &treeNode,
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


    void reset_inline_wrt_slicing(const solvert &solver, call_tree_nodet &treeNode, partitioning_target_equationt &equation);

  void set_inline_sum(call_tree_nodet& summary);
};

/*******************************************************************\
 Function: get_refine_mode

 Purpose: Determining the refinement mode from a string.
\*******************************************************************/

inline refinement_modet get_refine_mode(const std::string& str)
{
    if (str == "force-inlining" || str == "0"){
        return refinement_modet::FORCE_INLINING;
    } else if (str == "random-substitution" || str == "1"){
        return refinement_modet::RANDOM_SUBSTITUTION;
    } else if (str == "slicing-result" || str == "2"){
        return refinement_modet::SLICING_RESULT;
    } else {
        // by default
        return refinement_modet::SLICING_RESULT;
    }
}

#endif
