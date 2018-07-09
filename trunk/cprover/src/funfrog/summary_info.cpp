/*******************************************************************

 Module: Keeps current state of the assertion checking in progress,
 i.e., to each function call it assigns a level of summarization 
 used in the symex analysis.

 Author: Ondrej Sery

\*******************************************************************/

#include "summary_info.h"
#include "assertion_info.h"
#include <util/std_expr.h>


void call_tree_nodet::set_initial_precision(
        const summary_precisiont default_precision,
        const std::function<bool(const std::string &)> & has_summary,
        const unsigned last_assertion_loc)
{
  for (auto & call_site : call_sites)
  {
    call_tree_nodet& function = call_site.second;
    std::string function_id = id2string(function.get_function_id());

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
      if (has_summary(function_id)) {
        // If summaries are present, we use them
        function.set_summary();
      }
      else {
        // Otherwise, we use the initial substitution scenario
        function.set_precision(default_precision);
      }
    }
    
    // Recursive traversal of func (DFS) 
    function.set_initial_precision(
            default_precision, has_summary, last_assertion_loc);
  }
}

bool call_tree_nodet::mark_enabled_assertions(
        const assertion_infot& assertion, unsigned depth,
        bool parent_stack_matches, const unsigned last_assertion_loc)
{
  assertion_in_subtree = false;

  for (call_sitest::iterator it = call_sites.begin();
          it != call_sites.end(); ++it) 
  {
    call_tree_nodet& function = it->second;
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

const goto_programt::const_targett* call_tree_nodet::get_target()
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

//unsigned call_tree_nodet::get_subtree_size(const goto_functionst & goto_functions){
//    unsigned res = goto_functions.function_map.at(function_id).body.instructions.size();
//    for (call_sitest::iterator it = call_sites.begin();
//         it != call_sites.end(); ++it)
//    {
//        res += it->second.get_subtree_size(goto_functions);
//    }
//    return res;
//}
