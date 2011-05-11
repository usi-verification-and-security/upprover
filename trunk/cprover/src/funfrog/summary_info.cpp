/*******************************************************************

 Module: Keeps current state of the assertion checking in progress,
 i.e., to each function call it assigns a level of summarization 
 used in the symex analysis.

 Author: Ondrej Sery

\*******************************************************************/

#include <std_expr.h>
#include "summary_info.h"

void
call_summaryt::set_inline(const summarization_contextt &summarization_context,
        const irep_idt &target_function,
        const assertion_infot &assertion,
        unsigned int& summaries_inlined, size_t stack_depth, bool force_inlining)
{
  precision = INLINE;

  const goto_programt &function_body = 
    summarization_context.get_function(target_function).body;
  
  summary_info.initialize(summarization_context, function_body, assertion,
		  summaries_inlined, stack_depth++, force_inlining);
}

void
summary_infot::initialize(const summarization_contextt& summarization_context,
        const goto_programt& code, const assertion_infot& assertion,
        unsigned int& summaries_inlined, size_t stack_depth, bool force_inlining)
{
  bool will_inline = stack_depth < assertion.get_target_stack().size();
  goto_programt::const_targett call_pos;
  if (will_inline) {
    call_pos = assertion.get_target_stack().at(stack_depth);
  }
  // Find all call-sites and initialize them to a NONDET summary.
  // An exception are functions on the path to the target 
  // assertion.
  for(goto_programt::const_targett inst=code.instructions.begin();
      inst!=code.instructions.end(); ++inst)
  {
    if (inst->type == FUNCTION_CALL) {
      // NOTE: Expects the function call to by a standard symbol call
      const code_function_callt& function_call = to_code_function_call(inst->code);
      const irep_idt &target_function = to_symbol_expr(
        function_call.function()).get_identifier();
      // Mark the call site
      call_summaryt& call_summary = call_sites.insert(
              std::pair<goto_programt::const_targett, call_summaryt>(inst,
              call_summaryt())).first->second;
      call_summary.initialize(target_function);

      // Is the call on the call stack leading to the target assertion?
      if (will_inline && inst == call_pos) {
#       if 0
        std::cout << "Inlining a call: " << target_function << std::endl;
#       endif
        call_summary.set_inline(summarization_context, target_function,
                assertion, summaries_inlined, stack_depth+1, force_inlining);
      } else {
        const interpolantst& summaries = 
          summarization_context.get_summaries(target_function);
        if (summaries.size() > 0 && !force_inlining) {              // !force_inlining is used for inlining a function after substituting by a summary is failed
          call_summary.set_summary();
          summaries_inlined++;
        } else {
          call_summary.set_inline(summarization_context, target_function,
                assertion, summaries_inlined, stack_depth+1, force_inlining);
        }
        // call_summary.set_nondet();
#       if 0
        std::cout << "Havocing a call." << target_function << std::endl;
#       endif
      }
    }
  }
}
