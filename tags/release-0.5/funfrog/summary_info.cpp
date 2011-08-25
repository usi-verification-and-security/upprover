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
std::map<goto_programt::const_targett, std::vector<unsigned> > summary_infot::assertion_locs;
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
        const irep_idt &target_function,
        size_t stack_depth){
  summary_info.set_function_id(target_function);

  const goto_programt &function_body =
      summarization_context.get_function(target_function).body;
  summary_info.initialize(summarization_context, function_body,
                  stack_depth);
}

void summary_infot::initialize(
    const summarization_contextt& summarization_context, const goto_programt& code,
    size_t stack_depth)
{
  for(goto_programt::const_targett inst=code.instructions.begin();
      inst!=code.instructions.end(); ++inst)
  {
    global_loc++;
    if (inst->type == GOTO){
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

    else if (inst->type == FUNCTION_CALL) {
      // NOTE: Expects the function call to by a standard symbol call
      const code_function_callt& function_call = to_code_function_call(inst->code);
      const irep_idt &target_function = to_symbol_expr(
        function_call.function()).get_identifier();

      // Mark the call site
      call_summaryt& call_summary = call_sites.insert(
              std::pair<goto_programt::const_targett, call_summaryt>(inst,
              call_summaryt(this, stack_depth, global_loc)
              )).first->second;
      functions.push_back(&call_summary);

      call_summary.initialize(summarization_context, target_function,
                      stack_depth+1);
    }
    else if (inst->type == ASSERT){
      assertion_locs[inst].push_back(global_loc);
    }
  }
}

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
    const assertion_infot& assertion, unsigned i)
{
  const unsigned assertion_location = assertion_locs[assertion.get_location()].at(i);
  const unsigned assertion_stack_size = assertion.get_target_stack().size();

  for (unsigned i = 0; i < functions.size(); i++){

    const irep_idt &function_id = (*functions[i]).get_summary_info().get_function_id();
    const size_t function_depth = (*functions[i]).stack_depth;

    bool will_inline = function_depth < assertion_stack_size;
    if (will_inline) {
      const code_function_callt &call =
        to_code_function_call(to_code(assertion.get_target_stack().at(function_depth)->code));

      const irep_idt &ass_stack_call_id = call.function().get("identifier");
      (*functions[i]).call_stack = (will_inline && (ass_stack_call_id == function_id));
    }
    if ((*functions[i]).call_stack){
      (*functions[i]).set_inline();
    } else {
      const interpolantst& summaries =
        summarization_context.get_summaries(function_id);
      if (summaries.size() > 0) {
        (*functions[i]).set_summary();
      } else if ((*functions[i]).call_location > assertion_location) {
        (*functions[i]).set_nondet();
      } else {
        (*functions[i]).precision = default_precision;
      }
    }
  }
}

unsigned summary_infot::get_precision_count(summary_precisiont precision){
  unsigned count = 0;
  for (unsigned i = 0; i < functions.size(); i++){
    if ((*functions[i]).get_precision() == precision){
      count++;
    }
  }
  return count;
}
