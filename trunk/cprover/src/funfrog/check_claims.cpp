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


#include "check_claims.h"
#include "assertion_info.h"


/*******************************************************************

 Function: find_assertion

 Inputs:

 Outputs:

 Purpose: Starting from `start' we search for an assertion.
          `stack' keeps the call path to that assertion.

\*******************************************************************/
goto_programt::const_targett find_assertion(
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
         f_it->second.body.instructions.size()>0)
      {
        stack.push(it);
        it = f_it->second.body.instructions.begin();
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
  unsigned claim_nr,
  bool show_pass,
  bool show_fail,
  bool show_progress,
  bool save_files,
  bool use_smt)
{
  // precondition: the leaping program must be numbered correctly.
  claim_statst res;  

  unsigned inlined_claims = count_inlined_claims(leaping_program,
                                                 goto_functions);
  unsigned seen_claims = 0;
  
  res.total_claims = claim_map.size();
  
  std::string fname;

  call_stackt stack;
  goto_programt::const_targett ass_ptr=
    find_assertion(leaping_program.instructions.begin(),
                     goto_functions,
                     stack);
  
  if(claim_nr!=0)
  {
    while(claim_numbers[ass_ptr]!=claim_nr && 
          ass_ptr!=leaping_program.instructions.end())
      ass_ptr=find_assertion(ass_ptr,
                             goto_functions,
                             stack);
  }

  // NOTE: Not reimplemented yet
  // show_inlined_claimst show_inlined_claims(goto_functions,
  //                                          imprecise_loops,
  //                                          precise_loops,
  //                                          ns);

  while(ass_ptr!=leaping_program.instructions.end())
  {
    if(show_progress)
    {
      seen_claims++;
      std::cout << "\r    Checking Claim #" << claim_numbers[ass_ptr] << " (";
      std::cout << (int)(100*seen_claims/(double)inlined_claims);
      std::cout << "%) ...";
      std::cout.flush();
    }

    std::ofstream out;

    if(save_files)
    {
      fname = stats_dir + "claim_" + integer2string(claim_numbers[ass_ptr]);
      out.open(fname.c_str(), std::fstream::app);
      out << std::string(80, '-') << std::endl;
    }

    // NOTE: No inlining in FUNFROG
    // goto_programt::const_targett inlined_assertion =
    //   gil.goto_inline(stack, ass_ptr, out);
    //
    // if(inlined_program.instructions.size()>res.max_instruction_count)
    //  res.max_instruction_count=inlined_program.instructions.size();

    bool pass=false;
    
    if(!claim_map[ass_ptr].first || claim_map[ass_ptr].second)       
      pass = assertion_holds_sum(ns.get_context(),
          leaping_program,
          assertion_infot(stack, ass_ptr),
          out,
          res.max_mem_used,
          use_smt);
    else 
      pass = true;
      
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

    if(claim_nr!=0) break; // bail out

    // get the next assertion     
    ass_ptr = find_assertion(ass_ptr,
                             goto_functions,
                             stack);
  }
  
  if(show_progress)
  {
    std::cout << "\r" << std::string(80, ' ');
    std::cout.flush();
  }
  
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
  
  /*
  for(loopstoret::const_iterator lit=precise_loops.begin();
      lit!=precise_loops.end();
      lit++)
  {
    forall_goto_program_instructions(it, lit->second)
    {
      if(it->type==ASSERT)
      {
        claim_map[it] = std::make_pair(false, true);
        claim_numbers[it] = claim_map.size();
      }
    }
  }
  */
}

/*******************************************************************\

Function: get_claims

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void show_claims(const namespacet &ns,
                 const claim_mapt &claim_map, 
                 const claim_numberst &claim_numbers)
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
      
    const irep_idt &comment=it->second->location.get("comment");      
    const irep_idt description=
      (comment==""?"user supplied assertion":comment);
    
    claim_numberst::const_iterator nr_it = claim_numbers.find(it->second);
    std::cout << "Claim " << nr_it->second << ": " << description << std::endl;
    
    std::cout << "  At: " << it->second->location << std::endl;
    
    std::cout << it->second->location.get_function() << ":" <<      
                 it->second->location.get_line() << std::endl;
    
    std::cout << "  " << from_expr(ns, "", it->second->guard)
              << std::endl;
    std::cout << std::endl;  
  }
}
