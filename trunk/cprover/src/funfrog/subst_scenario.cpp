/*******************************************************************

 Module: An interface between summarizing checker and summary info,
         providing a precision level for all function calls
         of the given program

 Author: Grigory Fedyukovich

\*******************************************************************/

#include "subst_scenario.h"

void subst_scenariot::setup_default_precision(init_modet init)
{
  if (init == ALL_HAVOCING){
     default_precision = HAVOC;
   } else if (init == ALL_SUBSTITUTING){
     default_precision = INLINE;
   } else {
     assert(false);
   }
}

void subst_scenariot::initialize_call(
        call_summaryt& call_summary,
        const irep_idt &target_function)
{
  call_summary.get_summary_info().set_function_id(target_function);

  const goto_programt &function_body =
      summarization_context.get_function(target_function).body;
  initialize_summary_info(call_summary.get_summary_info(), function_body);
}

void subst_scenariot::initialize_summary_info(
    summary_infot& summary_info, const goto_programt& code)
{
  summary_info.get_assertions().clear();

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
      call_summaryt& call_summary = summary_info.get_call_sites().insert(
              std::pair<goto_programt::const_targett, call_summaryt>(inst,
              call_summaryt(&summary_info, global_loc)
              )).first->second;  //ToDo: refactor
      functions.push_back(&call_summary);

      initialize_call(call_summary, target_function);
    }
    else if (inst->type == ASSERT){
      summary_info.get_assertions()[inst] = global_loc;
    }
  }
}

unsigned subst_scenariot::get_precision_count(summary_precisiont precision)
{
  unsigned count = 0;
  for (unsigned i = 0; i < functions.size(); i++){
    if ((*functions[i]).get_precision() == precision){
      count++;
    }
  }
  return count;
}

// FIXME: This optimization seems to be broken for checking multiple assertions!
void subst_scenariot::process_goto_locations()
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
    unsigned loc = (*functions[i]).get_call_location();
    for (unsigned j = goto_sz; j < goto_ranges.size(); j++){
      std::pair<unsigned, unsigned> r = goto_ranges[j];
      if (r.first<= loc && loc <= r.second){
        loc = r.first;
      }
    }
    (*functions[i]).set_call_location(loc);
  }

  goto_ranges.clear();
}
