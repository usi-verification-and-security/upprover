/*******************************************************************

 Module: Loopfrog's final claim checking

 Author: CM Wintersteiger

\*******************************************************************/

#include <fstream>

#include <util/ui_message.h>
#include <util/xml.h>
#include <util/xml_irep.h>

#include <ansi-c/expr2c.h>
#include "core_checker.h"
#include "theory_refiner.h"
#include "check_claims.h"
/*******************************************************************

 Function: find_assertion

 Inputs:

 Outputs:

 Purpose: Starting from `start' we search for an assertion.
          `stack' keeps the call path to that assertion.

\*******************************************************************/
goto_programt::const_targett claim_statst::find_assertion(
  const goto_programt::const_targett &start,
  const goto_functionst &goto_functions,
  call_stackt &stack)
{
  goto_programt::const_targett it = start; it++;

  while(it->type!=ASSERT)
  {
    if(it->type==FUNCTION_CALL)
    {
      const code_function_callt &call =
        to_code_function_call(to_code(it->code));

      const irep_idt &name = call.function().get("identifier");

      goto_functionst::function_mapt::const_iterator f_it =
        goto_functions.function_map.find(name);

      if(f_it!=goto_functions.function_map.end() &&
         f_it->second.body.instructions.size()>0 &&
         !is_unwinding_exceeded(name) &&
         !is_recursion_unwinding(name))
      {
        stack.push(it);
        it = f_it->second.body.instructions.begin();
        increment_unwinding_counter(name);
      }
      else
        it++; // just ignore it
    }
    else if(it->type==OTHER)
    {
      if(it->is_other() &&
         it->code.get("statement")=="loop-summary")
      {
          // No loop summaries supported here
          assert(false);
      }
      else
        it++;
    }
    else if(it->type==END_FUNCTION)
    {
      const irep_idt &name = (it->code).get("identifier");
      decrement_unwinding_counter(name);
      if(stack.size()==0)
      {
        // this must be the end. 
        return (++it);
      }
      else
      {
        it = stack.top(); stack.pop();
        it++;
      }
    }
    else
      it++;
  }

  // `it' now points to the assertion, while
  // stack contains the call stack for this assertion
  return it;
}

/*******************************************************************\

Function: check_claims

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void check_claims(
  const goto_modelt & goto_model,
  claim_mapt &claim_map,
  claim_numberst &claim_numbers,
  const optionst& options,
  ui_message_handlert &_message_handler,
  unsigned claim_nr)
{
  // precondition: the leaping program must be numbered correctly.
  claim_statst res {options.get_unsigned_int_option("unwind")};
  unsigned inlined_claims =   999;//count_inlined_claims(leaping_program,
                                  //                 goto_functions); //ToDO: fix it (add unwind)
  unsigned seen_claims = 0;
  bool assert_grouping = !options.get_bool_option("no-assert-grouping");
  
  const std::string &set=options.get_option("claimset");
  unsigned int length=set.length();
  bool multi_assert = (length > 0);
  std::vector<unsigned> claims;

  if (multi_assert){
    for(unsigned idx=0; idx<length; idx++)
    {
      std::string::size_type next=set.find(",", idx);
      std::string val=set.substr(idx, next-idx);
      claims.push_back(atoi(val.c_str()));

      if(next==std::string::npos) break;
      idx=next;
    }
  }

  std::vector <goto_programt::const_targett> multi_assert_loc;

  res.set_message_handler(_message_handler);
  res.total_claims = claim_map.size();

  const auto & goto_functions = goto_model.goto_functions;
  const auto & main_body = goto_functions.function_map.at(goto_functionst::entry_point()).body;
  call_stackt stack;
  goto_programt::const_targett ass_ptr = main_body.instructions.begin();
  
  // NOTE: Not reimplemented yet
  // show_inlined_claimst show_inlined_claims(goto_functions,
  //                                          imprecise_loops,
  //                                          precise_loops,
  //                                          ns);




  if (options.get_bool_option("theoref")){

    // GF: currently works only for one assertion (either specified in --claim or the first one)
    while(ass_ptr != main_body.instructions.end() &&
              (claim_numbers[ass_ptr] != claim_nr) == (claim_nr != 0))
    {
      ass_ptr = res.find_assertion(ass_ptr, goto_functions, stack);
    }
      
    if (ass_ptr == main_body.instructions.end()){
      if (seen_claims == 0) // In case we set the multi assert mode working here
        res.status() << "\nAssertion is not reachable\n" << res.eom;
      return;
    }

    symbol_tablet temp_table;
    namespacet ns1(goto_model.symbol_table, temp_table);

    theory_refinert th_checker(main_body,
	        goto_functions, ns1, temp_table, options, _message_handler);

    th_checker.initialize();
    th_checker.assertion_holds_smt(ass_ptr, true);
    return;
  }

  core_checkert core_checker(main_body, goto_functions,
                            goto_model.symbol_table, options, _message_handler, res.max_mem_used);

  core_checker.initialize();

  if(options.get_bool_option("sum-theoref")){
      while(ass_ptr != main_body.instructions.end()){
          ass_ptr = res.find_assertion(ass_ptr, goto_functions, stack);
          if(ass_ptr == main_body.instructions.end()){
              break;
          }
          assert(claim_map.find(ass_ptr) != claim_map.end());
          res.status()  << " ---------checking the claim # " <<std::to_string(claim_numbers[ass_ptr]) <<" ---------"<< res.eom;
          bool single_res = core_checker.check_sum_theoref_single(ass_ptr);
          claim_map[ass_ptr] = std::make_pair(true, single_res);
      }
      // REPORT the results
      res.status() << "\n--------- OVERAL VERIFICATION STATISTICS ---------\n" <<res.eom;
      std::map<claim_numberst::mapped_type, claim_numberst::key_type> flipped;
      for(const auto & entry : claim_numbers){
          flipped[entry.second] = entry.first;
      }
      for (const auto & entry : flipped) {
          auto claim_number = entry.first;
          const auto & assertion = entry.second;
          const auto & claim_res = claim_map.at(assertion);
          bool checked = claim_res.first;
          bool safe = claim_res.second;
          if (checked){
              res.status() << "Claim number # " <<  claim_number << " is " << (safe ? "SAFE" : "UNSAFE") << res.eom;

              res.status()
              <<" File: " << assertion->source_location.get_file()
              <<" \n Function: " << assertion->source_location.get_function()
              <<" \n Line: " << assertion->source_location.get_line()
              << "\n " << ((assertion->is_assert()) ? "Guard: " : "Code") <<"( "
              << from_expr(assertion->guard) <<" ) \n";
          }
          else {
              res.status() << "Claim number " <<  claim_number << " has not been checked!";
          }
          res.status() << res.eom;
      }
      return;
  }

  if (options.get_bool_option("all-claims") || options.get_bool_option("claims-opt")){
    core_checker.assertion_holds(assertion_infot(), true);
  } else while(true) {
    // Next assertion (or next occurrence of the same assertion)
    ass_ptr = res.find_assertion(ass_ptr, goto_functions, stack);
    while(ass_ptr != main_body.instructions.end() &&
            (claim_numbers[ass_ptr] != claim_nr) == (claim_nr != 0))
    {
      ass_ptr = res.find_assertion(ass_ptr, goto_functions, stack);
    }
    if (ass_ptr == main_body.instructions.end()){
      if (seen_claims == 0)
        res.status() << "\nAssertion is not reachable\n" << res.eom;
      break;

    }
    if (assert_grouping && claim_map[ass_ptr].first)
      continue;
    
    if(!multi_assert)
    {
      seen_claims++;
      res.status() << (std::string("\r    Checking Claim #") + std::to_string(claim_numbers[ass_ptr]) + std::string(" (") +
    		    std::to_string((int)(100*seen_claims/(double)(assert_grouping ? claim_numbers.size() : inlined_claims))) +
    		    std::string("%) ...")) << res.eom;
    }

    bool pass = false;
    if (multi_assert){
      bool ok = false;
      for (unsigned i = 0; i < claims.size(); i++){
        if (claims[i] == claim_numbers[ass_ptr]){
          ok = true;
          break;
        }
      }
      if (ok){
        multi_assert_loc.push_back(ass_ptr);
      }
    } else {
      pass = core_checker.assertion_holds(assert_grouping ?
              assertion_infot(ass_ptr) : assertion_infot(stack, ass_ptr), false);
    }

    claim_map[ass_ptr].first = true;
    
    if (pass)
    {
      claim_map[ass_ptr].second = true;
    }
    else
    {
      claim_map[ass_ptr].second = false;
    }
  }

  if (multi_assert){
    res.status() << "Checking claims: ";
    for (unsigned i = 0; i < claims.size(); i++){
      res.status() << "\"" << claims[i] <<"\"";
      if (i < claims.size() - 1){
        res.status() << ", ";
      }
    }
    res.status() << " in a multi_assertion mode.\r" << res.eom;
    core_checker.assertion_holds(assert_grouping ?
                  assertion_infot(multi_assert_loc) : assertion_infot(stack, ass_ptr), false);
  }
}


/*******************************************************************\

Function: get_claims

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void get_claims(
  const goto_functionst &goto_functions,
  claim_mapt &claim_map,
  claim_numberst &claim_numbers)
{    
  forall_goto_functions(fit, goto_functions)
  {
    if(!fit->second.is_inlined())
      forall_goto_program_instructions(it, fit->second.body)
      {
        if(it->type==ASSERT)
        {
          claim_map[it] = std::make_pair(false, true);
          claim_numbers[it] = claim_map.size();
        }
      }
  }
}

/*******************************************************************\

Function: get_claims

  Inputs:

 Outputs:

 Purpose: Not in use

\*******************************************************************/

/*
void show_claims(const namespacet &ns,
                 const claim_mapt &claim_map, 
                 const claim_numberst &claim_numbers,
                 ui_message_handlert::uit ui)
{
  std::map<unsigned, goto_programt::const_targett> reverse_map;
  for(claim_numberst::const_iterator it=claim_numbers.begin();
      it!=claim_numbers.end();
      it++)
  {
    reverse_map[it->second] = it->first;
  }
  
  for(std::map<unsigned, goto_programt::const_targett>::const_iterator it=
        reverse_map.begin();
      it!=reverse_map.end();
      it++)
  {
    assert(it->second->type==ASSERT);

    const source_locationt &location=it->second->source_location; // KE: locationt is now source_locationt (in CBMC 5.5)
      
    const irep_idt &comment=location.get_comment();
    const irep_idt &function=location.get_function();
    const irep_idt &property=location.get_property_id(); // KE: was just get_property(), can be either get_property_id or get_property_class
    const irep_idt &line=location.get_line();
    const irep_idt &file=location.get_file();
    const irep_idt description=
      (comment==""?"assertion":comment);

    claim_numberst::const_iterator nr_it = claim_numbers.find(it->second);

    std::string claim_name = std::to_string(nr_it->second);
    
    switch(ui)
    {
      case ui_message_handlert::uit::XML_UI:
      {
        xmlt xml("claim");
        xml.new_element("number").data=claim_name;
        xml.new_element("name").data=claim_name;

        xmlt &l=xml.new_element();
        convert(location, l);
        l.name="location";

        l.new_element("line").data=id2string(line);
        l.new_element("file").data=id2string(file);
        l.new_element("function").data=id2string(function);

        xml.new_element("description").data=id2string(description);
        xml.new_element("property").data=id2string(property);
        xml.new_element("expression").data=from_expr(ns, "", it->second->guard);

        std::cout << xml << std::endl;
      }
      break;

      case ui_message_handlert::uit::PLAIN:
      {
        const irep_idt description=
          (comment==""?"user supplied assertion":comment);

        std::cout << "Claim " << claim_name << ": " << description << std::endl;

        std::cout << "  At: " << location << std::endl;

        //std::cout << function << ":" << line << std::endl;

        std::cout << "  Guard: " << from_expr(ns, "", it->second->guard) << std::endl;

        std::cout << std::endl;
      }
      break;

    default:
      assert(false);
    }
  }
}
*/

void store_claims(const claim_mapt &claim_map,
                 const claim_numberst &claim_numbers)
{
  std::ofstream mapping;
  mapping.open ("__mapping");

  std::map<unsigned, goto_programt::const_targett> reverse_map;
  for(claim_numberst::const_iterator it=claim_numbers.begin();
      it!=claim_numbers.end();
      it++)
  {
    reverse_map[it->second] = it->first;
  }

  for(std::map<unsigned, goto_programt::const_targett>::const_iterator it=
        reverse_map.begin();
      it!=reverse_map.end();
      it++)
  {
    assert(it->second->type==ASSERT);

    mapping << std::to_string(claim_numbers.find(it->second)->second) << " "
        << (it->second->source_location).get_property_id().c_str() << std::endl; // KE: get_claim doesn't exist anymore - I think all just becomes a property
  }
}
