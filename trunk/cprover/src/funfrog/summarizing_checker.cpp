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
#include "summary_info.h"
#include "symex_assertion_sum.h"

#include "solvers/satcheck_opensmt.h"

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
  const goto_functionst &goto_functions,
  std::ostream &out,
  unsigned long &max_memory_used,
  bool use_smt)
{
  contextt temp_context;
  namespacet ns(context, temp_context);
  summarizing_checkert sum_checker(value_sets, head,
          goto_functions, loopstoret(), loopstoret(), ns, temp_context);

  return sum_checker.last_assertion_holds(goto_program, out,
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
  const goto_functionst &goto_functions,
  const assertion_infot& assertion,
  std::ostream &out,
  unsigned long &max_memory_used,
  bool use_smt)
{
  contextt temp_context;
  namespacet ns(context, temp_context);
  goto_programt::const_targett first = goto_program.instructions.begin();
  summarizing_checkert sum_checker(value_set_analysist(ns),
                         first, goto_functions, loopstoret(), loopstoret(),
                         ns, temp_context);

  return sum_checker.assertion_holds(goto_program, assertion, out,
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
  const goto_functionst &goto_functions,
  const assertion_infot& assertion,
  std::ostream &out,
  unsigned long &max_memory_used,
  bool use_smt)
{
  contextt temp_context;
  namespacet ns(context, temp_context);
  summarizing_checkert sum_checker(value_sets, head, goto_functions,
          loopstoret(), loopstoret(), ns, temp_context);

  return sum_checker.assertion_holds(goto_program, assertion, out,
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

  // Prepare the summarization context
  summarization_contextt summarization_context(goto_functions, value_sets,
          imprecise_loops, precise_loops);
  summarization_context.analyze_functions(ns);

  // Load older summaries
  summarization_context.deserialize_infos("__summaries");

  // Prepare summary_info, start with the lazy variant, i.e.,
  // all summaries are initialized as NONDET except those on the way
  // to the target assertion, which are marked INLINE.
  summary_infot summary_info;
  summary_info.initialize(summarization_context, goto_program, assertion);

  // Prepare the decision and interpolation procedures
  std::auto_ptr<prop_convt> decider;
  std::auto_ptr<interpolating_solvert> interpolator;
  {
    satcheck_opensmtt* opensmt = new satcheck_opensmtt();
    bv_pointerst *deciderp = new bv_pointerst(ns, *opensmt);
    deciderp->unbounded_array = bv_pointerst::U_AUTO;
    decider.reset(deciderp);
    interpolator.reset(opensmt);
  }

  // TODO: In loop call symex_assertion_sum, with refining 
  // the summary_info based on the spurious counter-examples 
  // (or ad hoc at first)
  partitioning_target_equationt equation(ns);
  symex_assertion_sumt symex = symex_assertion_sumt(
          summarization_context,
          summary_info,
          original_loop_head,
          ns,
          context,
          *decider,
          *interpolator,
          equation
          );

  // FIXME: The refinement loop should be here!
  bool result = symex.assertion_holds(goto_program, assertion,
          std::cout /* FIXME: out */, max_memory_used, use_smt);

  if (result) {
    // Extract the interpolation summaries here...
    interpolant_mapt itp_map;
    equation.extract_interpolants(*interpolator, *decider, itp_map);

    for (interpolant_mapt::iterator it = itp_map.begin();
            it != itp_map.end(); ++it) {
      irep_idt& function_id = it->first;
      if (!it->second.is_trivial()) {
        summarization_context.get_function_info(function_id).add_summary(it->second);
      }
    }

    // Store the summaries
    summarization_context.serialize_infos("__summaries");
  }

  return result;
}

