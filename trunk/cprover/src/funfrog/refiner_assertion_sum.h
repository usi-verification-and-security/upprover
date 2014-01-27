/*******************************************************************
 Module: Refining schema for function summarization.
         Supposed to have different implementations.

 Author: Grigory Fedyukovich

 \*******************************************************************/

#ifndef CPROVER_REFINER_ASSERTION_SUM_H
#define CPROVER_REFINER_ASSERTION_SUM_H

#include "assertion_info.h"
#include "subst_scenario.h"
#include "summary_info.h"
#include "summarization_context.h"
#include "partitioning_target_equation.h"

#ifdef USE_PERIPLO
#include "solvers/satcheck_periplo.h"
#else
#include "solvers/satcheck_opensmt.h"
#endif

class refiner_assertion_sumt:public messaget
{
public:
  refiner_assertion_sumt(
          summarization_contextt &_summarization_context,
          subst_scenariot &_omega,
          partitioning_target_equationt &_target,
          refinement_modet _mode,
          message_handlert &_message_handler,
          //std::ostream &_out,
          const unsigned _last_assertion_loc,
          bool _valid
          ) :
          summarization_context(_summarization_context),
          omega(_omega),
          equation(_target),
          mode(_mode),
          //out(_out),
          message_handler(_message_handler),
          last_assertion_loc(_last_assertion_loc),
          valid (_valid)
          {set_message_handler(_message_handler);};

  void refine(prop_convt& decider, summary_infot& summary);
  std::list<summary_infot*>& get_refined_functions(){ return refined_functions; }
  void set_refine_mode(refinement_modet _mode){ mode = _mode; }

protected:
  // Shared information about the program and summaries to be used during
  // analysis
  summarization_contextt &summarization_context;

  // substituting scenario
  subst_scenariot &omega;

  // Store for the symex result
  partitioning_target_equationt &equation;

  // Mode of refinement
  refinement_modet mode;

  // Default output
  //std::ostream &out;
  message_handlert &message_handler;

  // Location of the last assertion to be checked
  const unsigned last_assertion_loc;

  // Mode of changing the summaries validity
  bool valid;

  std::list<summary_infot*> refined_functions;

  void reset_inline(summary_infot& summary);
  void reset_random(summary_infot& summary);
  void reset_depend(prop_convt& decider, summary_infot& summary);

  // not in use now
  void reset_depend_rec(std::vector<summary_infot*>& dep, summary_infot& summary);

  void set_inline_sum(summary_infot& summary);
};

#endif
