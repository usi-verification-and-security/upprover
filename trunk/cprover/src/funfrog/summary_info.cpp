/*******************************************************************

 Module: Keeps current state of the assertion checking in progress,
 i.e., to each function call it assigns a level of summarization 
 used in the symex analysis.

 Author: Ondrej Sery

\*******************************************************************/

#include <std_expr.h>
#include "summary_info.h"

summary_precisiont summary_infot::default_precision = INLINE;

void call_summaryt::set_precision_deep(
        summary_precisiont _precision,
        const summarization_contextt &summarization_context,
        const irep_idt &target_function,
        const assertion_infot &assertion,
        size_t stack_depth,
        bool _call_stack)
{
  precision = _precision;
  call_stack = _call_stack;

  const goto_programt &function_body =
    summarization_context.get_function(target_function).body;
  
  summary_info.initialize(summarization_context, function_body, assertion,
		  stack_depth++);
}

void summary_infot::set_default_precision(init_modet init)
{
  if (init == ALL_HAVOCING){
     summary_infot::default_precision = NONDET;
   } else if (init == ALL_SUBSTITUTING){
     summary_infot::default_precision = INLINE;
   } else {
     assert(false);
   }
}

void
summary_infot::initialize(const summarization_contextt& summarization_context,
        const goto_programt& code, const assertion_infot& assertion,
        size_t stack_depth)
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
              call_summaryt(this))).first->second;
      call_summary.initialize(target_function);

      // Is the call on the call stack leading to the target assertion?
      if (will_inline && inst == call_pos) {
        call_summary.set_precision_deep(INLINE, summarization_context, target_function,
                assertion, stack_depth+1, true);
      } else {
        const interpolantst& summaries = 
          summarization_context.get_summaries(target_function);
        if (summaries.size() > 0) {
          call_summary.set_precision_deep(SUMMARY, summarization_context, target_function,
              assertion, stack_depth+1);
        } else {
          call_summary.set_precision_deep(default_precision, summarization_context, target_function,
                assertion, stack_depth+1);
        }
      }
    }
  }
}
