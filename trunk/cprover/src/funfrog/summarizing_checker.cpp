/*******************************************************************

 Module: Assertion checker that extracts and uses function 
 summaries

 Author: Ondrej Sery

\*******************************************************************/

#include <memory>

#include <goto-symex/build_goto_trace.h>
#include <find_symbols.h>
#include <ansi-c/expr2c.h>
#include <time_stopping.h>
#include <pointer-analysis/value_set_analysis.h>
#include <solvers/sat/satcheck.h>
#include <solvers/smt1/smt1_dec.h>
#include <loopfrog/memstat.h>

#include "summarizing_checker.h"

/*******************************************************************

 Function: last_assertion_holds

 Inputs:

 Outputs:

 Purpose: Checks if the last assertion of the GP holds. This is only
 a convenience wrapper.

\*******************************************************************/

bool last_assertion_holds_sum(
  const contextt &context,
  const value_setst &value_sets,
  goto_programt::const_targett &head,
  const goto_programt &goto_program,
  std::ostream &out,
  unsigned long &max_memory_used,
  bool use_smt)
{
  contextt temp_context;
  namespacet ns(context, temp_context);
  summarizing_checkert symex(value_sets, head, loopstoret(), loopstoret(), ns, temp_context);

  return symex.last_assertion_holds(goto_program, out,
                                    max_memory_used, use_smt);
}

/*******************************************************************

 Function: summarizing_checkert::last_assertion_holds

 Inputs:

 Outputs:

 Purpose: Checks if the last assertion of the GP holds. This is only
 a convenience wrapper.

\*******************************************************************/

bool summarizing_checkert::last_assertion_holds(
  const goto_programt &goto_program,
  std::ostream &out,
  unsigned long &max_memory_used,
  bool use_smt)
{
  assert(!goto_program.empty() &&
         goto_program.instructions.rbegin()->type==ASSERT);

  goto_programt::const_targett last=goto_program.instructions.end(); last--;
  call_stackt empty_stack;
  assertion_infot assertion(empty_stack, last);

  return assertion_holds(goto_program, assertion, 
          out, max_memory_used, use_smt);
}

/*******************************************************************

 Function: assertion_holds_sum

 Inputs:

 Outputs:

 Purpose: Checks if the given assertion of the GP holds (without 
 value sets). This is only a convenience wrapper.

\*******************************************************************/

bool assertion_holds_sum(
  const contextt &context,
  const goto_programt &goto_program,
  const assertion_infot& assertion,
  std::ostream &out,
  unsigned long &max_memory_used,
  bool use_smt)
{
  contextt temp_context;
  namespacet ns(context, temp_context);
  goto_programt::const_targett first = goto_program.instructions.begin();
  summarizing_checkert symex(value_set_analysist(ns),
                         first, loopstoret(), loopstoret(),
                         ns, temp_context);

  return symex.assertion_holds(goto_program, assertion, out,
                               max_memory_used, use_smt);
}

/*******************************************************************

 Function: assertion_holds_sum

 Inputs:

 Outputs:

 Purpose: Checks if the given assertion of the GP holds. This is only
 a convenience wrapper.

\*******************************************************************/

bool assertion_holds_sum(
  const contextt &context,
  const value_setst &value_sets,
  goto_programt::const_targett &head,
  const goto_programt &goto_program,
  const assertion_infot& assertion,
  std::ostream &out,
  unsigned long &max_memory_used,
  bool use_smt)
{
  contextt temp_context;
  namespacet ns(context, temp_context);
  summarizing_checkert symex(value_sets, head, loopstoret(), loopstoret(), 
          ns, temp_context);

  return symex.assertion_holds(goto_program, assertion, out,
                               max_memory_used, use_smt);
}

/*******************************************************************

 Function: summarizing_checkert::assertion_holds

 Inputs:

 Outputs:

 Purpose: Checks if the given assertion of the GP holds

\*******************************************************************/

bool summarizing_checkert::assertion_holds(
  const goto_programt &goto_program,
  const assertion_infot& assertion,
  std::ostream &out,
  unsigned long &max_memory_used,
  bool use_smt)
{
  // Trivial case
  if(assertion.get_location()->guard.is_true())
  {
    out << std::endl << "ASSERTION IS TRUE" << std::endl;
    return true;
  }

  // TODO: Prepare summary_info, start with lazy variant

  // TODO: In loop call symex_assertion_sum, with refining 
  // the summary_info based on the spurious counter-examples 
  // (or ad hoc at first)

  return false;
}

