/*******************************************************************

 Module: Keeps current state of the assertion checking in progress,
 i.e., to each function call it assigns a level of summarization 
 used in the symex analysis.

 Author: Ondrej Sery

\*******************************************************************/

#include <util/std_expr.h>
#include "summary_info.h"
#include "summarization_context.h"

void summary_infot::set_initial_precision(
    summary_precisiont default_precision,
    const unsigned last_assertion_loc,
    const summarization_contextt& summarization_context,
    const assertion_infot& assertion)
{
  assert(is_root());
  set_initial_precision(default_precision,
      summarization_context, last_assertion_loc);
}

// This method should when enabled assertions are filled in, i.e., after a call
// to mark_enabled_assertions()
void summary_infot::set_initial_precision(
    summary_precisiont default_precision,
    const summarization_contextt& summarization_context,
    const unsigned last_assertion_loc)
{
  for (call_sitest::iterator it = call_sites.begin();
          it != call_sites.end(); ++it) 
  {
    summary_infot& function = it->second;
    const irep_idt& function_id = function.get_function_id();

    if (function.is_recursion_nondet()){
      function.set_nondet();
    } else if (function.has_assertion_in_subtree()) {
      // If assertion is in the subtree, we need to inline the call.
      function.set_inline();
    } 
    else if (function.get_call_location() > last_assertion_loc
        || function.is_unwind_exceeded())
    {
      // If the call is after the last assertion (including also backward gotos)
      // we can safely ignore it
      function.set_nondet();
    }
    else 
    {
      const summary_idst& summaries =
              summarization_context.get_summaries(function_id);

      if (summaries.size() > 0) {
        // If summaries are present, we use them
        function.set_summary();
      }
      else {
        // Otherwise, we use the initial substitution scenario
        function.set_precision(default_precision);
      }
    }
    
    // Recursive traversal
    function.set_initial_precision(
            default_precision, summarization_context, last_assertion_loc);
  }
}

bool summary_infot::mark_enabled_assertions(
        const assertion_infot& assertion, unsigned depth,
        bool parent_stack_matches, const unsigned last_assertion_loc)
{
  assertion_in_subtree = false;

  for (call_sitest::iterator it = call_sites.begin();
          it != call_sites.end(); ++it) 
  {
    summary_infot& function = it->second;
    const irep_idt& function_id = function.get_function_id();
    bool current_stack_matches = assertion.stack_matches(function_id, depth,
            parent_stack_matches);
    
    // Recursive traversal
    assertion_in_subtree |= function.mark_enabled_assertions(
            assertion, depth+1, current_stack_matches, last_assertion_loc);
  }

  enabled_assertions.clear();
  if (last_assertion_loc >= call_location) {
    for (location_mapt::const_iterator it = assertions.begin();
            it != assertions.end(); ++it)
    {
      if (assertion.assertion_matches(depth, it->first)) {
        if (assertion.is_assert_grouping() || parent_stack_matches){
          // FIXME: it is still not the most precise way to determine
          //        different the call stack of current assertion instance
          enabled_assertions.insert(it->first);
          assertion_in_subtree = true;
        }
      }
    }
  }
  
  return assertion_in_subtree;
}

const goto_programt::const_targett* summary_infot::get_target()
{
  call_sitest& parent_call_sites = get_parent().get_call_sites();
  for (call_sitest::iterator it = parent_call_sites.begin();
          it != parent_call_sites.end(); ++it)
  {
    if (&(it->second) == this)
      return &(it->first);
  }
  assert(false);
  return NULL;
}

unsigned summary_infot::get_subtree_size(const summarization_contextt& summarization_context){
    unsigned res = summarization_context.get_function(function_id).body.instructions.size();
    for (call_sitest::iterator it = call_sites.begin();
         it != call_sites.end(); ++it)
    {
        res += it->second.get_subtree_size(summarization_context);
    }
    return res;
}
