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
    location_visitedt& assertions_visited,
    const summarization_contextt& summarization_context,
    const assertion_infot& assertion)
{
  assert(is_root());
  std::map<unsigned, bool> &vis = assertions_visited[assertion.get_location()];
  unsigned last_assertion_loc = 0;

  if (!assertion.is_assert_grouping()){
    for (std::map<unsigned, bool>::iterator it = vis.begin(); it != vis.end(); ++it){
        // if no-grouping, every time we search for single instance of
        // the assertion, not visited before (with min location)
        if (it-> second == false){
          if (it->first < last_assertion_loc || last_assertion_loc == 0){
            last_assertion_loc = it->first;
            vis[last_assertion_loc] = true;
          }
        }
    }
  } else {
    for (std::map<unsigned, bool>::iterator it = vis.begin(); it != vis.end(); ++it){
      // if grouping, we must include all instances of the assertion,
      // so therefore we search for the max location
      if (it->first > last_assertion_loc){
        last_assertion_loc = it->first;
      }
    }
  }

  mark_enabled_assertions(summarization_context, assertion, 0, true);
  set_initial_precision(default_precision,
      summarization_context, assertion, last_assertion_loc);
}

// This method should when enabled assertions are filled in, i.e., after a call
// to mark_enabled_assertions()
void summary_infot::set_initial_precision(
    summary_precisiont default_precision,
    const summarization_contextt& summarization_context,
    const assertion_infot& assertion, unsigned last_assertion_loc)
{
  for (call_sitest::iterator it = call_sites.begin();
          it != call_sites.end(); ++it) 
  {
    summary_infot& function = it->second;
    const irep_idt& function_id = function.get_function_id();
    
    if (function.has_assertion_in_subtree()) {
      // If assertion is in the subtree, we need to inline the call.
      function.set_inline();
    } 
    else if (function.get_call_location() > last_assertion_loc)
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
            default_precision, summarization_context, assertion, last_assertion_loc);
  }
}

bool summary_infot::mark_enabled_assertions(
        const summarization_contextt& summarization_context,
        const assertion_infot& assertion, unsigned depth,
        bool parent_stack_matches)
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
            summarization_context, assertion, depth+1,
            current_stack_matches);
  }

  enabled_assertions.clear();
  for (location_mapt::const_iterator it = assertions.begin();
          it != assertions.end(); ++it) 
  {
    if (assertion.assertion_matches(depth, it->first)) {
      enabled_assertions.insert(it->first);
      assertion_in_subtree = true;
    }
  }
  
  return assertion_in_subtree;
}
