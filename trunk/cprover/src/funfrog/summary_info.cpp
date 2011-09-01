/*******************************************************************

 Module: Keeps current state of the assertion checking in progress,
 i.e., to each function call it assigns a level of summarization 
 used in the symex analysis.

 Author: Ondrej Sery

\*******************************************************************/

#include <std_expr.h>
#include "summary_info.h"

void summary_infot::set_initial_precision(
    summary_precisiont default_precision,
//    location_mapt& assertions,
    const summarization_contextt& summarization_context,
    const assertion_infot& assertion, bool assert_grouping)
{
  assert(is_root());
  unsigned last_assertion_loc = 0;
  mark_enabled_assertions(/*assertions,*/ summarization_context, assertion, 0, true,
          assert_grouping, last_assertion_loc);
  set_initial_precision(default_precision,// assertions,
      summarization_context, assertion, last_assertion_loc);
}

// This method should when enabled assertions are filled in, i.e., after a call
// to mark_enabled_assertions()
void summary_infot::set_initial_precision(
    summary_precisiont default_precision,
//    location_mapt& assertions,
    const summarization_contextt& summarization_context,
    const assertion_infot& assertion, unsigned last_assertion_loc)
{
  for (call_sitest::iterator it = call_sites.begin();
          it != call_sites.end(); ++it) 
  {
    call_summaryt& function = it->second;
    const irep_idt& function_id = function.get_summary_info().get_function_id();
    
    if (function.summary_info.has_assertion_in_subtree()) {
      // If assertion is in the subtree, we need to inline the call.
      function.set_inline();
    } 
    else if (function.call_location > last_assertion_loc) 
    {
      // If the call is after the last assertion (including also backward gotos)
      // we can safely ignore it
      function.set_nondet();
    }
    else 
    {
      const summariest& summaries =
              summarization_context.get_summaries(function_id);

      if (summaries.size() > 0) {
        // If summaries are present, we use them
        function.set_summary();
      }
      else {
        // Otherwise, we use the initial substitution scenario
        function.precision = default_precision;
      }
    }
    
    // Recursive traversal
    function.get_summary_info().set_initial_precision(
            default_precision, //assertions,
            summarization_context, assertion, last_assertion_loc);
  }
}

// Does the call stack match the current stack? If we group all assertions
// regardless the stack, this just returns the same value as the parent stack 
// frame.
bool stack_matches(const assertion_infot& assertion, 
        const irep_idt& function_id, unsigned depth,
        bool parent_stack_matches, bool assert_grouping) 
{
  if (assert_grouping)
    return parent_stack_matches;
  
  bool stack_matches = parent_stack_matches && 
          (depth < assertion.get_target_stack().size());

  // Does the callstack prefix match callstack of the assertion to be checked
  if (stack_matches) {
    const code_function_callt &call =
      to_code_function_call(to_code(assertion.get_target_stack().at(depth)->code));
    const irep_idt &ass_stack_call_id = call.function().get("identifier");
      
    stack_matches = ass_stack_call_id == function_id;
  }
  
  return stack_matches;
}

// Does the given assertion match the one to be currently analyzed?
bool assertion_matches(const assertion_infot& assertion, unsigned depth,
        const goto_programt::const_targett& current_assertion,
        bool assert_grouping) 
{
  if (!assert_grouping && depth != assertion.get_target_stack().size()) {
    return false;
  }
  
  return assertion.get_location() == current_assertion;
}

bool summary_infot::mark_enabled_assertions(
        //location_mapt& assertions,
        const summarization_contextt& summarization_context,
        const assertion_infot& assertion, unsigned depth,
        bool parent_stack_matches, bool assert_grouping,
        unsigned& last_assertion_loc)
{
  assertion_in_subtree = false;

  for (call_sitest::iterator it = call_sites.begin();
          it != call_sites.end(); ++it) 
  {
    call_summaryt& function = it->second;
    const irep_idt& function_id = function.get_summary_info().get_function_id();
    bool current_stack_matches = stack_matches(assertion, function_id, depth,
            parent_stack_matches, assert_grouping);
    
    // Recursive traversal
    assertion_in_subtree |= function.get_summary_info().mark_enabled_assertions(
            /*assertions,*/ summarization_context, assertion, depth+1,
            current_stack_matches, assert_grouping, last_assertion_loc);
  }
  
  enabled_assertions.clear();
  for (location_mapt::const_iterator it = assertions.begin();
          it != assertions.end(); ++it) 
  {
    if (assertion_matches(assertion, depth, it->first, assert_grouping)) {
      enabled_assertions.insert(it->first);
      if (it->second > last_assertion_loc) {
        last_assertion_loc = it->second;
      }
      assertion_in_subtree = true;
    }
  }
  
  return assertion_in_subtree;
}
