/*******************************************************************

 Module: Loopfrog's final claim checking

 Author: CM Wintersteiger

\*******************************************************************/

#include <ansi-c/expr2c.h>

#include "symex_assertion.h"
#include "conditional_goto_copy.h"
#include "localized_inlining.h"
#include "inlined_claims.h"

#include "check_claims.h"

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
  const loopstoret &imprecise_loops,
  const loopstoret &precise_loops,
  const std::string &stats_dir,
  claim_mapt &claim_map,
  claim_numberst &claim_numbers,
  unsigned claim_nr,
  bool show_pass,
  bool show_fail,
  bool show_progress,
  bool save_files,
  bool assume_guarantee,
  bool check_by_invariant,
  bool use_smt)
{
  // precondition: the leaping program must be numbered correctly.
  stream_message_handlert message_handler(std::cout);
  claim_statst res;  

  unsigned inlined_claims = count_inlined_claims(leaping_program,
                                                 goto_functions,
                                                 imprecise_loops,
                                                 precise_loops);
  unsigned seen_claims = 0;
  
  res.total_claims = claim_map.size();
  
  std::string fname;

  call_stackt stack;
  goto_programt::const_targett ass_ptr=
    find_assertion(leaping_program.instructions.begin(),
                     goto_functions,
                     imprecise_loops,
                     precise_loops,
                     stack);
  
  if(claim_nr!=0)
  {
    while(claim_numbers[ass_ptr]!=claim_nr && 
          ass_ptr!=leaping_program.instructions.end())
      ass_ptr=find_assertion(ass_ptr,
                             goto_functions,
                             imprecise_loops,
                             precise_loops,
                             stack);
  }

  goto_programt inlined_program;

  goto_inline_localizedt::progresst inlining_progress(leaping_program,
                                                      inlined_program,
                                                      assume_guarantee);

  goto_inline_localizedt gil(goto_functions,
                             inlining_progress,
                             imprecise_loops,
                             precise_loops,
                             ns);

  show_inlined_claimst show_inlined_claims(goto_functions,
                                           imprecise_loops,
                                           precise_loops,
                                           ns);

  while(ass_ptr!=leaping_program.instructions.end())
  {
    if(show_progress)
    {
      seen_claims++;
      std::cout << "\r    Checking Claim #" << claim_numbers[ass_ptr] << " (";
      printf("%.0f", 100*seen_claims/(double)inlined_claims);
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

    goto_programt::const_targett inlined_assertion =
      gil.goto_inline(stack, ass_ptr, out);

    if(inlined_program.instructions.size()>res.max_instruction_count)
      res.max_instruction_count=inlined_program.instructions.size();


    bool pass=false;
    
    if (check_by_invariant)
      pass = inlined_assertion->guard.is_true();
    else
    {
      if(/* !checked || safe */
         !claim_map[ass_ptr].first || claim_map[ass_ptr].second)       
        pass = assertion_holds(ns.get_context(),
            inlined_program,
            inlined_assertion,
            out,
            res.max_mem_used,
            use_smt);
      else 
        pass = true;
      
      claim_map[ass_ptr].first = true;
    }
    
    if (pass)
    {
      if (show_pass)
      {
        std::cout << "\rPASSED: ";
        show_inlined_claims.show_claim(inlined_assertion, stack,
                                       claim_numbers[ass_ptr], std::cout);
      }
    }
    else
    {      
      if (show_fail)
      {
        std::cout << "\rFAILED: ";
        show_inlined_claims.show_claim(inlined_assertion, stack,
                                       claim_numbers[ass_ptr], std::cout);
      }
      
      claim_map[ass_ptr].second = false;
    }

    if(save_files)
      out.close();

    if(claim_nr!=0) break; // bail out

    // get the next assertion     
    ass_ptr = find_assertion(ass_ptr,
                             goto_functions,
                             imprecise_loops,
                             precise_loops,
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

Function: check_claims_using_domain

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

claim_statst check_claims_using_domain(
  const namespacet &ns,
  goto_functionst &goto_functions,
  const invariant_propagation_adaptort &invariant_propagation,
  bool simplify_claims)
{
  claim_statst res;

  Forall_goto_functions(f_it, goto_functions)  
  {
    Forall_goto_program_instructions(it, f_it->second.body)
    {
      if(it->type==ASSERT)
      {
        res.total_claims++;
        if (invariant_propagation.implies_claim(it))
        {
          if (simplify_claims)
            //it->make_skip();
            it->guard.make_true();
          res.claims_passed++;
        }
        else
          res.claims_failed++;
      }
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
  const loopstoret &precise_loops,
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
