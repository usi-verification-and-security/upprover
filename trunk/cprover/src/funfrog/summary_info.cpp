/*******************************************************************

 Module: Keeps current state of the assertion checking in progress,
 i.e., to each function call it assigns a level of summarization 
 used in the symex analysis.

 Author: Ondrej Sery

\*******************************************************************/

#include <std_expr.h>
#include "summary_info.h"

summary_precisiont summary_infot::default_precision = INLINE;
std::vector<call_summaryt*> summary_infot::functions (NULL);
std::vector<std::pair<unsigned, unsigned> > summary_infot::goto_ranges (NULL);
unsigned summary_infot::global_loc = 0;

void summary_infot::setup_default_precision(init_modet init)
{
  if (init == ALL_HAVOCING){
     summary_infot::default_precision = HAVOC;
   } else if (init == ALL_SUBSTITUTING){
     summary_infot::default_precision = INLINE;
   } else {
     assert(false);
   }
}

void call_summaryt::initialize(
        const summarization_contextt &summarization_context,
        const irep_idt &target_function)
{
  summary_info.set_function_id(target_function);

  const goto_programt &function_body =
      summarization_context.get_function(target_function).body;
  summary_info.initialize(summarization_context, function_body);
}

void summary_infot::initialize(
    const summarization_contextt& summarization_context, const goto_programt& code)
{
  assertions.clear();
  
  for(goto_programt::const_targett inst=code.instructions.begin();
      inst!=code.instructions.end(); ++inst)
  {
    global_loc++;
    
    if (inst->type == GOTO)
    {
      unsigned tmp_location = inst->location_number;
      unsigned max_location = tmp_location;
      unsigned min_location = tmp_location;

      for(goto_programt::targetst::const_iterator it = inst->targets.begin();
          it!=inst->targets.end();
          it++)
      {
        unsigned tgt_location = (*it)->location_number;
        if(tgt_location < min_location){
          min_location = tgt_location;
        }
        if(tgt_location > max_location){
          max_location = tgt_location;
        }
      }

      if (min_location != max_location){
        goto_ranges.push_back(std::make_pair(
             global_loc - (tmp_location - min_location),
             global_loc + (max_location - tmp_location)));
      }
    }
    else if (inst->type == FUNCTION_CALL) 
    {
      // NOTE: Expects the function call to by a standard symbol call
      const code_function_callt& function_call = to_code_function_call(inst->code);
      const irep_idt &target_function = to_symbol_expr(
        function_call.function()).get_identifier();

      // Mark the call site
      call_summaryt& call_summary = call_sites.insert(
              std::pair<goto_programt::const_targett, call_summaryt>(inst,
              call_summaryt(this, global_loc)
              )).first->second;
      functions.push_back(&call_summary);

      call_summary.initialize(summarization_context, target_function);
    }
    else if (inst->type == ASSERT){
      assertions[inst] = global_loc;
    }
  }
}

// FIXME: This optimization seems to be broken for checking multiple assertions!
void summary_infot::process_goto_locations()
{
  const unsigned goto_sz = goto_ranges.size();
  if (goto_sz == 0){
    return;
  }
  for (unsigned i = 0; i < goto_sz; i++){
    std::pair<unsigned, unsigned>& r = goto_ranges[i];
    for (unsigned j = 0; j < goto_sz; j++){
      std::pair<unsigned, unsigned>& q = goto_ranges[j];
      if (r.first < q.first){
        std::pair<unsigned, unsigned> t = r;
        r = q;
        q = t;
      }
    }
  }

  unsigned min = goto_ranges[0].first;
  unsigned max = goto_ranges[0].second;

  for (unsigned i = 1; i < goto_sz; i++){
    if (goto_ranges[i].first <= max) {
      if (goto_ranges[i].second > max) {
        max = goto_ranges[i].second;
      }
    } else {
      goto_ranges.push_back(std::make_pair(min, max));
      min = goto_ranges[i].first;
      max = goto_ranges[i].second;
    }
  }
  goto_ranges.push_back(std::make_pair(min, max));

  for (unsigned i = 0; i < functions.size(); i++){
    unsigned loc = (*functions[i]).call_location;
    for (unsigned j = goto_sz; j < goto_ranges.size(); j++){
      std::pair<unsigned, unsigned> r = goto_ranges[j];
      if (r.first<= loc && loc <= r.second){
        loc = r.first;
      }
    }
    (*functions[i]).call_location = loc;
  }

  goto_ranges.clear();
}

void summary_infot::set_initial_precision(
    const summarization_contextt& summarization_context,
    const assertion_infot& assertion, bool assert_grouping)
{
  assert(is_root());
  unsigned last_assertion_loc = 0;
  mark_enabled_assertions(summarization_context, assertion, 0, true, 
          assert_grouping, last_assertion_loc);
  set_initial_precision(summarization_context, assertion, last_assertion_loc);
}

// This method should when enabled assertions are filled in, i.e., after a call
// to mark_enabled_assertions()
void summary_infot::set_initial_precision(
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
      const interpolantst& summaries =
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
            summarization_context, assertion, last_assertion_loc);
  }
}

unsigned summary_infot::get_precision_count(summary_precisiont precision) 
{
  unsigned count = 0;
  for (unsigned i = 0; i < functions.size(); i++){
    if ((*functions[i]).get_precision() == precision){
      count++;
    }
  }
  return count;
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
            summarization_context, assertion, depth+1, current_stack_matches, 
            assert_grouping, last_assertion_loc);
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
