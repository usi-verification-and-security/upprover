/*******************************************************************

 Module: Loopfrog's final claim checking

 Author: CM Wintersteiger

\*******************************************************************/

#include <fstream>
#include <ansi-c/expr2c.h>

#include "summarizing_checker.h"
#include "inlined_claims.h"
/*
#include "conditional_goto_copy.h"
#include "localized_inlining.h"
*/

#include <xml.h>
#include <i2string.h>
#include <xml_irep.h>

#include "check_claims.h"
#include <ui_message.h>


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
  call_stackt &stack,
  unsigned unwind)
{
  goto_programt::const_targett it = start; it++;

  while(it->type!=ASSERT)
  {
    if(it->type==FUNCTION_CALL)
    {
      const code_function_callt &call =
        to_code_function_call(to_code(it->code));

      const irep_idt &name = call.function().get("identifier");

      set_function_to_be_unwound(name);

      goto_functionst::function_mapt::const_iterator f_it =
        goto_functions.function_map.find(name);

      if(f_it!=goto_functions.function_map.end() &&
         f_it->second.body.instructions.size()>0 &&
         !is_unwinding_exceeded(unwind))
      {
        stack.push(it);
        it = f_it->second.body.instructions.begin();
        increment_unwinding_counter();
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
      decrement_unwinding_counter();
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

claim_statst check_claims(
  const namespacet &ns,
  goto_programt &leaping_program,
  const goto_functionst &goto_functions,
  const std::string &stats_dir,
  claim_mapt &claim_map,
  claim_numberst &claim_numbers,
  const optionst& options,
  ui_message_handlert &_message_handler,
  unsigned claim_nr,
  bool show_pass,
  bool show_fail,
  bool show_progress,
  bool save_files)
{
  // precondition: the leaping program must be numbered correctly.
  claim_statst res;  
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

  std::string fname;
  call_stackt stack;
  goto_programt::const_targett ass_ptr = leaping_program.instructions.begin();
  
  // NOTE: Not reimplemented yet
  // show_inlined_claimst show_inlined_claims(goto_functions,
  //                                          imprecise_loops,
  //                                          precise_loops,
  //                                          ns);


  contextt temp_context;
  namespacet ns1(ns.get_context(), temp_context);
  summarizing_checkert sum_checker(leaping_program, value_set_analysist(ns1),
        goto_functions, ns1, temp_context, options, _message_handler, res.max_mem_used);

  sum_checker.initialize();

  if (options.get_bool_option("all-claims")){
    sum_checker.assertion_holds(assertion_infot(), true);
  } else while(true) {
    // Next assertion (or next occurrence of the same assertion)
    ass_ptr = res.find_assertion(ass_ptr, goto_functions, stack, options.get_int_option("unwind"));
    while(ass_ptr != leaping_program.instructions.end() && 
            (claim_numbers[ass_ptr] != claim_nr) == (claim_nr != 0))
    {
      ass_ptr = res.find_assertion(ass_ptr, goto_functions, stack, options.get_int_option("unwind"));
    }
    if (ass_ptr == leaping_program.instructions.end()) 
      break;
    
    if (assert_grouping && claim_map[ass_ptr].first)
      continue;
    
    if(show_progress && !multi_assert)
    {
      seen_claims++;
      res.status(std::string("\r    Checking Claim #") + i2string(claim_numbers[ass_ptr]) + std::string(" (") +
    		    i2string((int)(100*seen_claims/(double)(assert_grouping ? claim_numbers.size() : inlined_claims))) +
    		    std::string("%) ..."));
    }

    std::ofstream out;

    if(save_files)
    {
      fname = stats_dir + "claim_" + i2string(claim_numbers[ass_ptr]);
      out.open(fname.c_str(), std::fstream::app);
      out << std::string(80, '-') << std::endl;
    }

    // NOTE: No inlining in FUNFROG
    // goto_programt::const_targett inlined_assertion =
    //   gil.goto_inline(stack, ass_ptr, out);
    //
    // if(inlined_program.instructions.size()>res.max_instruction_count)
    //  res.max_instruction_count=inlined_program.instructions.size();



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
      pass = sum_checker.assertion_holds(assert_grouping ?
              assertion_infot(ass_ptr) : assertion_infot(stack, ass_ptr), false);
    }

    claim_map[ass_ptr].first = true;
    
    if (pass)
    {
      if (show_pass)
      {
        // NOTE: Not reimplemented yet
        // std::cout << "\rPASSED: ";
        // show_inlined_claims.show_claim(inlined_assertion, stack,
        //                                claim_numbers[ass_ptr], std::cout);
      }

      claim_map[ass_ptr].second = true;
    }
    else
    {      
      if (show_fail)
      {
        // NOTE: Not reimplemented yet
        // std::cout << "\rFAILED: ";
        // show_inlined_claims.show_claim(inlined_assertion, stack,
        //                                claim_numbers[ass_ptr], std::cout);
      }
      
      claim_map[ass_ptr].second = false;
    }

    if(save_files)
      out.close();
  }

  if (multi_assert){
    std::cout << "Checking claims: ";
    for (unsigned i = 0; i < claims.size(); i++){
      std::cout << "\"" << claims[i] <<"\"";
      if (i < claims.size() - 1){
        std::cout << ", ";
      }
    }
    std::cout << " in a multi_assertion mode.\r\n";
    sum_checker.assertion_holds(assert_grouping ?
                  assertion_infot(multi_assert_loc) : assertion_infot(stack, ass_ptr), false);
  }

//  if(show_progress)
//  {
//    std::cout << "\r" << std::string(80, ' ');
//    std::cout.flush();
//  }
  
  for(claim_mapt::const_iterator it=claim_map.begin();
      it!=claim_map.end();
      it++)
  {
    if(claim_nr==0 || claim_numbers[it->first]==claim_nr)
    {
      if(it->second.second) res.claims_passed++; else res.claims_failed++;
    }
  }

  return res;
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

 Purpose:

\*******************************************************************/

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

    const locationt &location=it->second->location;
      
    const irep_idt &comment=location.get_comment();
    const irep_idt &function=location.get_function();
    const irep_idt &property=location.get_property();
    const irep_idt description=
      (comment==""?"assertion":comment);

    claim_numberst::const_iterator nr_it = claim_numbers.find(it->second);

    std::string claim_name = i2string(nr_it->second);
    
    switch(ui)
    {
    case ui_message_handlert::XML_UI:
      {
        xmlt xml("claim");
        xml.new_element("number").data=claim_name;
        xml.new_element("name").data=claim_name;

        xmlt &l=xml.new_element();
        convert(location, l);
        l.name="location";

        l.new_element("line").data=id2string(location.get_line());
        l.new_element("file").data=id2string(location.get_file());
        l.new_element("function").data=id2string(location.get_function());

        xml.new_element("description").data=id2string(description);
        xml.new_element("property").data=id2string(property);
        xml.new_element("expression").data=from_expr(ns, "", it->second->guard);

        std::cout << xml << std::endl;
      }
      break;

    case ui_message_handlert::PLAIN:
      {
        const irep_idt &comment=it->second->location.get("comment");
        const irep_idt description=
          (comment==""?"user supplied assertion":comment);

        std::cout << "Claim " << nr_it->second << ": " << description << std::endl;

        std::cout << "  At: " << it->second->location << std::endl;

        std::cout << it->second->location.get_function() << ":" <<
                     it->second->location.get_line() << std::endl;

        std::cout << "  " << from_expr(ns, "", it->second->guard)
                  << std::endl;
        std::cout << std::endl;
      }
      break;

    default:
      assert(false);
    }
  }
}
