/*******************************************************************

 Module: Inlined Claims Handling

 Author: CM Wintersteiger

 \*******************************************************************/

#include <list>
#include <stack>
#include <ostream>
#include <arith_tools.h>

#include "inlined_claims.h"

/*******************************************************************\

Function: show_inlined_claimst::show

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void show_inlined_claimst::show(
  const goto_programt &program, 
  std::ostream &out)
{
  forall_goto_program_instructions(it, program)
  {
    if(it->type==ASSERT)
    {
      show_claim(it, call_stack, ++claim_count, out); 
    }
    else if(it->type==FUNCTION_CALL)
    {
      const code_function_callt &call = 
        to_code_function_call(to_code(it->code));
      
      const irep_idt name = call.function().get("identifier");
      
      goto_functionst::function_mapt::const_iterator f_it = 
        functions.function_map.find(name);
      
      if(f_it!=functions.function_map.end())
      {
        call_stack.push(it);
        show(f_it->second.body, out);
        call_stack.pop();
      }
    }
    else if(it->type==OTHER)
    {
      const codet &code = to_code(it->code);
      if(code.get_statement()=="loop-summary")
      {
        mp_integer inx_mp = string2integer(code.get("index").as_string(), 10);
        unsigned long inx = inx_mp.to_ulong();
        
        loopstoret::const_iterator s_it = precise_loops.find(inx);
        
        if(s_it!=precise_loops.end())
        {
          call_stack.push(it);
          show(s_it->second, out);
          call_stack.pop();
        } 
        else
          throw "Invalid loop-summary index";
      }
    }
  }
}

/*******************************************************************\

Function: show_inlined_claimst::find_marked_claim

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

unsigned find_marked_claim(
  const goto_functionst &functions,
  const loopstoret &precise_loops,
  const irep_idt &mark,
  const claim_numberst &claim_numbers)
{
  std::stack<goto_programt::const_targett> stack;
  
  unsigned holdoff=0;
  
  const std::string &mstring = mark.as_string();
  size_t p=mstring.rfind("_");
  if(p!=std::string::npos)
  {
    holdoff = atoi(mstring.substr(p+1).c_str());    
  }

  forall_goto_functions(fit, functions)
  {
    forall_goto_program_instructions(it, fit->second.body)
    {
      if(find(it->labels.begin(), it->labels.end(), mark)!=it->labels.end())
      {
        while(it->type!=ASSERT) it++;
        claim_numberst::const_iterator nr_it=claim_numbers.find(it);
        assert(nr_it!=claim_numbers.end());
        return nr_it->second + holdoff;
      }
    }
  }
  
  for(loopstoret::const_iterator lit=precise_loops.begin();
      lit!=precise_loops.end();
      lit++)
  {
    forall_goto_program_instructions(it, lit->second)
    {
      if(find(it->labels.begin(), it->labels.end(), mark)!=it->labels.end())
      {
        while(it->type!=ASSERT) it++;
        claim_numberst::const_iterator nr_it=claim_numbers.find(it);
        assert(nr_it!=claim_numbers.end());
        return nr_it->second + holdoff;
      }
    }
  }
  
  return (unsigned) -1;
}

/*******************************************************************\

Function: show_inlined_claimst::show_claim

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void show_inlined_claimst::show_claim(
  goto_programt::const_targett &it,
  const call_stackt &call_stack,
  unsigned claim_nr,
  std::ostream &out) const
{
  assert(it->type==ASSERT);
  
  const irep_idt &comment=it->location.get("comment");      
  const irep_idt description=
    (comment==""?"user supplied assertion":comment);
  
  std::cout << "Claim " << claim_nr << ": " << description << std::endl;
  
  std::cout << "  At: " << it->location << std::endl;
  
  if(call_stack.size()>0)
  {
    std::cout << "  Call path: ";      
    for(call_stackt::const_iterator l_it = ++call_stack.begin();
        l_it!=call_stack.end();
        l_it++)
    {
      if((*l_it)->type==FUNCTION_CALL)
      {
        const symbolt &sym=ns.lookup((*l_it)->function);      
        std::cout << sym.pretty_name << ":" << 
          (*l_it)->location.get_line() << " -> ";
      }
      else if((*l_it)->type==OTHER)
      {
        const codet &code = to_code((*l_it)->code);
        std::cout << "LOOP-SUMMARY" << ":" << 
          code.get("index") << " -> ";
      }
        
    }
  }
  
  std::cout << it->location.get_function() << ":" <<      
               it->location.get_line() << std::endl;
  
  std::cout << "  " << from_expr(ns, "", it->guard)
            << std::endl;
  std::cout << std::endl;     
}

/*******************************************************************\

Function: show_inlined_claims

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void show_inlined_claims(
  const goto_programt &program, 
  const goto_functionst &functions,
  const loopstoret &imprecise_loops,
  const loopstoret &precise_loops,
  const namespacet &ns,
  std::ostream &out) 
{
  show_inlined_claimst sic(functions,imprecise_loops,precise_loops,ns);
  sic.show(program, out);
  
  if(sic.claim_count==0) std::cout << std::endl << "No claims." << std::endl;
}

/*******************************************************************\

Function: count_inlined_claims

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

unsigned count_inlined_claims(
  const goto_programt &program, 
  const goto_functionst &functions,
  const loopstoret &imprecise_loops,
  const loopstoret &precise_loops) 
{
  unsigned res=0;
    
  forall_goto_program_instructions(it, program)
  {
    if(it->type==ASSERT)
      res++;
    else if(it->type==FUNCTION_CALL)
    {
      const code_function_callt &call = 
        to_code_function_call(to_code(it->code));
      
      const irep_idt name = call.function().get("identifier");
      
      goto_functionst::function_mapt::const_iterator f_it = 
        functions.function_map.find(name);
      
      if(f_it!=functions.function_map.end())
        res += count_inlined_claims(f_it->second.body, 
                                    functions,
                                    imprecise_loops,
                                    precise_loops);
    }
    else if(it->type==OTHER)
    {
      const codet &code = to_code(it->code);
      if(code.get_statement()=="loop-summary")
      {
        mp_integer inx_mp = string2integer(code.get("index").as_string(), 10);
        unsigned long inx = inx_mp.to_ulong();
        
        loopstoret::const_iterator s_it = precise_loops.find(inx);
        
        if(s_it!=precise_loops.end())
        {
          res += count_inlined_claims(s_it->second, 
                                      functions,
                                      imprecise_loops,
                                      precise_loops);
        }
        else
          throw "Invalid loop-summary index";
      }
    }
  }
  
  return res;
}
