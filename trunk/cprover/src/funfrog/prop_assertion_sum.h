/*******************************************************************
 Module: Propositional encoding of an SSA-form,
         And checking of its satisfiability

 Author: Ondrej Sery

 \*******************************************************************/

#ifndef CPROVER_PROP_ASSERTION_SUM_H
#define CPROVER_PROP_ASSERTION_SUM_H

#include <solvers/flattening/sat_minimizer.h>
#include <namespace.h>

#include <time_stopping.h>
#include <fstream>

#include "assertion_info.h"
#include "summarization_context.h"
#include "partitioning_target_equation.h"

extern fine_timet global_satsolver_time;
extern fine_timet global_sat_conversion_time;

class prop_assertion_sumt
{
public:
  prop_assertion_sumt(
          summarization_contextt& _summarization_context,
          partitioning_target_equationt &_target,
          std::ostream &_out,
          unsigned long &_max_memory_used
          ) :
          summarization_context(_summarization_context),
          equation(_target),
          solving_time(0),
          out(_out),
          max_memory_used(_max_memory_used)
          {};

  bool assertion_holds(const assertion_infot &assertion, const namespacet &ns, prop_convt& decider, interpolating_solvert& interpolator);

  const fine_timet& get_solving_time() { return solving_time; };

private:
  // Summarizing context (summary_store needed)
  summarization_contextt& summarization_context;

  // Store for the symex result
  partitioning_target_equationt &equation;

  // SAT solving time
  fine_timet solving_time;

  std::ostream &out;

  unsigned long &max_memory_used;

  bool is_satisfiable(decision_proceduret &decision_procedure);

};
#endif
