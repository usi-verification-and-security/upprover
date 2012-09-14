/*******************************************************************

 Module: An interface between summarizing checker and summary info,
         providing a precision level for all function calls
         of the given program

 Author: Grigory Fedyukovich

\*******************************************************************/

#include "subst_scenario.h"
#include <stdlib.h>
#include <string.h>

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
    	proc_count++;
      // NOTE: Expects the function call to by a standard symbol call
      const code_function_callt& function_call = to_code_function_call(inst->code);
      const irep_idt &target_function = to_symbol_expr(
        function_call.function()).get_identifier();
      set_function_to_be_unwound(target_function);

      // Mark the call site
      summary_infot& call_site = summary_info.get_call_sites().insert(
              std::pair<goto_programt::const_targett, summary_infot>(inst,
              summary_infot(&summary_info, global_loc)
              )).first->second;
      functions.push_back(&call_site);

      call_site.set_function_id(target_function);
//      call_site.set_order(functions.size());

      const goto_programt &function_body =
          summarization_context.get_function(target_function).body;

      if(!is_unwinding_exceeded(summarization_context.get_unwind_max())){


        increment_unwinding_counter();
        initialize_summary_info(call_site, function_body);
      } else {
        call_site.set_unwind_exceeded(true);
        //std::cout << "Recursion unwinding for " << target_function << " (" << inst->location << ") FINIFSHED with " << rec_unwind[target_function] << " iterations\n";
      }
    }
    else if (inst->type == END_FUNCTION){
      decrement_unwinding_counter();
    }
    else if (inst->type == ASSERT){
      summary_info.get_assertions()[inst] = global_loc;
      assertions_visited[inst][global_loc] = false;
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

unsigned subst_scenariot::get_precision_count(summary_infot& summary, summary_precisiont precision)
{
  unsigned res = 0;
  if (!summary.is_root()){
    for (call_sitest::iterator it = summary.get_call_sites().begin();
            it != summary.get_call_sites().end(); ++it)
    {
      if ((it->second).get_precision() == precision){
        res++;
      }
      res += get_precision_count(it->second, precision);
    }
  }
  return res;
}

void subst_scenariot::process_goto_locations()
{
  const unsigned goto_sz = goto_ranges.size();
  if (goto_sz == 0){
    return;
  }
  for (unsigned i = 0; i < goto_sz; i++){
    std::pair<unsigned, unsigned>& r = goto_ranges[i];
    for (unsigned j = i + 1; j < goto_sz; j++){
      std::pair<unsigned, unsigned>& q = goto_ranges[j];
      if (r.first > q.first){
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

//  for (unsigned i = 0; i < functions.size(); i++){
//    unsigned loc = (*functions[i]).get_call_location();
//    for (unsigned j = goto_sz; j < goto_ranges.size(); j++){
//      std::pair<unsigned, unsigned> r = goto_ranges[j];
//      if (r.first <= loc && loc <= r.second){
//        loc = r.first;
//      }
//    }
//    (*functions[i]).set_call_location(loc);
//  }

  goto_ranges.clear();
}

void subst_scenariot::setup_last_assertion_loc(const assertion_infot& assertion){
  last_assertion_loc = 0;
  int count = 0;
  if (assertion.is_all_assert()){
    for (location_visitedt::iterator it = assertions_visited.begin(); it != assertions_visited.end(); ++it){
      for (std::map<unsigned, bool>::iterator it2 = it->second.begin(); it2 != it->second.end(); ++it2){
        if (last_assertion_loc < it2->first){
          last_assertion_loc = it2->first;
          count++;
        }
      }
    }
    //std::cout << "Assertion not specified. Check whole program. " << std::endl;
  } else if (assertion.is_multi_assert()){
    const std::vector <goto_programt::const_targett>& multi_location = assertion.get_multi_location();
    for (unsigned i = 0; i < multi_location.size(); i++){
      std::map<unsigned, bool> &vis = assertions_visited[multi_location[i]];
      for (std::map<unsigned, bool>::iterator it = vis.begin(); it != vis.end(); ++it){
        if (it->first > last_assertion_loc){
          last_assertion_loc = it->first;
          count++;
        }
      }
    }

  } else {
    std::map<unsigned, bool> &vis = assertions_visited[assertion.get_location()];
    //std::cout << vis.size() << " instances of the assertion found." << std::endl;
    if (!assertion.is_assert_grouping()){
      for (std::map<unsigned, bool>::iterator it = vis.begin(); it != vis.end(); ++it){
          // if no-grouping, every time we search for single instance of
          // the assertion, not visited before (with min location)
          if (it-> second == false){

            if (it->first < last_assertion_loc || last_assertion_loc == 0){
              last_assertion_loc = it->first;
              vis[last_assertion_loc] = true;
              count = 1;
            }
          }
      }
    } else {
      for (std::map<unsigned, bool>::iterator it = vis.begin(); it != vis.end(); ++it){
        // if grouping, we must include all instances of the assertion,
        // so therefore we search for the max location
        if (it->first > last_assertion_loc){
          last_assertion_loc = it->first;
          count++;
        }
      }
    }
  }

  for (unsigned j = 0; j < goto_ranges.size(); j++){
    std::pair<unsigned, unsigned> r = goto_ranges[j];
    if (r.first <= last_assertion_loc && last_assertion_loc <= r.second){
      last_assertion_loc = r.second;
    }
  }
  //std::cout << "Last assertion location: " << last_assertion_loc << " / " << global_loc << " ( " << proc_count << ")" << std::endl;

  single_assertion_check = count == 1;

  functions_root.mark_enabled_assertions(assertion, 0, true, last_assertion_loc);
}

void serialize_used_summaries(std::ofstream& out, 
        const summary_ids_sett& used_summaries) 
{
  if (used_summaries.empty()) {
    out << "-" << std::endl;
    return;
  }
  
  bool first = true;
  for (summary_ids_sett::const_iterator it = used_summaries.begin();
          it != used_summaries.end(); ++it) {
    if (first) first = false;
    else {
      out << ",";
    }
    out << *it;
  }
  out << std::endl;
}

void deserialize_used_summaries(const std::string& line, 
        summary_ids_sett& used_summaries) 
{
  used_summaries.clear();
  
  if (line.length() == 0)
    return;
  
  char bfr[line.length()+1];
  char *start, *end = bfr;
  strcpy(bfr, line.c_str());
  
  for (;;) {
    start = end;
    
    while (*end != ',' && *end != 0) end++;
    bool last = *end == 0;
    
    *end++ = 0;
    summary_idt sid = atoi(start);
    
    used_summaries.insert(sid);
    
    if (last)
      break;
  }
}

void subst_scenariot::serialize(const std::string& file)
{
  std::ofstream out;
  out.open(file.c_str());

  if (out.fail()) {
    std::cerr << "Failed to serialize the substituting scenario (file: "
        << file << " cannot be accessed)." << std::endl;
    return;
  }

  for (unsigned i = 0; i < functions.size(); i++) {
    const summary_infot& info = *functions[i];
    out << info.get_function_id() << std::endl;
    out << info.get_call_location() << std::endl;
    out << info.get_precision() << std::endl;
    out << info.is_preserved_node() << std::endl;
    out << info.is_preserved_edge() << std::endl;
    out << info.has_assertion_in_subtree() << std::endl;
    serialize_used_summaries(out, info.get_used_summaries());
//    call_sitest call_sites = (*functions[i]).get_call_sites();
//    for (call_sitest::iterator it = call_sites.begin();
//            it != call_sites.end(); ++it)
//    {
//      out << " " << it->second.get_order();
//    }
  }

  if (out.fail()) {
    throw "Failed to serialize the substituting scenario.";
  }

  out.close();
}

void subst_scenariot::deserialize(
    const std::string& file, const goto_programt& code)
{
  std::vector<std::string> tmp;
  std::ifstream in;
  in.open(file.c_str());
  while (!in.eof() && !in.fail()){
    std::string str;
    in >> str;
    if (!str.empty()) tmp.push_back(str);
  }
  in.close();
  global_loc = 0;
  functions.clear();
  assertions_visited.clear();
  assert(tmp.size() % 7 == 0);
  restore_summary_info(functions_root, code, tmp);
}

void subst_scenariot::restore_summary_info(
    summary_infot& summary_info, const goto_programt& code, std::vector<std::string>& data)
{
  summary_info.get_assertions().clear();

  for(goto_programt::const_targett inst=code.instructions.begin();
      inst!=code.instructions.end(); ++inst)
  {
    global_loc++;

    if (inst->type == FUNCTION_CALL)
    {
      summary_infot& call_site = summary_info.get_call_sites().insert(
              std::pair<goto_programt::const_targett, summary_infot>(inst,
              summary_infot(&summary_info, global_loc)
              )).first->second;

      functions.push_back(&call_site);

      const irep_idt &target_function = data[(functions.size()-1)*7];
      call_site.set_function_id(target_function);
      switch (atoi(data[(functions.size()-1)*7+2].c_str())){
        case 0: {call_site.set_precision(HAVOC);} break;
        case 1: {call_site.set_precision(SUMMARY);} break;
        case 2: {call_site.set_precision(INLINE);} break;
      }

      if (data[(functions.size()-1)*7+3] == "1") { call_site.set_preserved_node(); }
      if (data[(functions.size()-1)*7+4] == "1") { call_site.set_preserved_edge(); }
      if (data[(functions.size()-1)*7+5] == "1") { call_site.set_assertion_in_subtree(); }
      
      if (data[(functions.size()-1)*7+6] != "-") {
        summary_ids_sett used_summaries;
        deserialize_used_summaries(data[(functions.size()-1)*7+6], used_summaries);
        call_site.set_used_summaries(used_summaries);
      }

      const goto_programt &function_body =
          summarization_context.get_function(target_function).body;
      restore_summary_info(call_site, function_body, data);
    }
    else if (inst->type == ASSERT){
      summary_info.get_assertions()[inst] = global_loc;
      assertions_visited[inst][global_loc] = false;
    }
  }
}

void subst_scenariot::construct_xml_tree(xmlt& call, summary_infot& summary)
{
  for (call_sitest::iterator it = summary.get_call_sites().begin();
          it != summary.get_call_sites().end(); ++it)
  {
    xmlt sub_call("function");
    sub_call.set_attribute("id", (it->second).get_function_id().c_str());
    sub_call.set_attribute_bool("old_summary",
         !summarization_context.any_invalid_summaries((it->second).get_function_id()));
    construct_xml_tree(sub_call, it->second);
    call.new_element(sub_call);
  }
}

void subst_scenariot::serialize_xml(const std::string& file)
{
  xmlt xml_head("program");
  construct_xml_tree(xml_head, functions_root);
  std::ofstream out;
  out.open(file.c_str());
  xml_head.output(out);
}
