/*******************************************************************\

Module: Slicer for local claims/variables

Author: Daniel Kroening, kroening@kroening.com
        CM Wintersteiger

\*******************************************************************/

#include <i2string.h>
#include <find_symbols.h>
#include <std_code.h>

#include "local_slicer.h"

class local_slicing_data_entryt
{
public:
  local_slicing_data_entryt()
  {
  }

  goto_programt::const_targetst successors;
  std::set<irep_idt> nondets;
};

/*******************************************************************\

Function: compute_predecessors

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void local_predecessors(
  goto_programt &goto_program,
  goto_programt::const_targetst &predecessors,
  goto_programt::const_targett PC)
{
  goto_programt::const_targett next_PC(PC);
  next_PC++;
  
  const goto_programt::instructiont &instruction=*PC;
  
  if(instruction.is_goto() || instruction.is_start_thread())
  {
    for(goto_programt::instructiont::targetst::const_iterator
        t_it=instruction.targets.begin();
        t_it!=instruction.targets.end();
        t_it++)
    {
      goto_programt::const_targett t=*t_it;
      if(t!=goto_program.instructions.end())
        predecessors.push_back(PC);
    }
  
    if(next_PC!=goto_program.instructions.end())
      predecessors.push_back(PC);
  }
  else if(next_PC!=goto_program.instructions.end())
    predecessors.push_back(PC);
}

/*******************************************************************\

Function: nondet_slicer

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void nondet_slicer(
  goto_programt &goto_program)
{
//  const goto_programt::local_variablest &scope=target->local_variables;
  
  std::map<goto_programt::const_targett, local_slicing_data_entryt>
    slicing_data;
    
  std::list<goto_programt::const_targett> queue;
  
//  for(code_typet::argumentst::const_iterator ait=
//        code_type.arguments().begin();
//      ait!=code_type.arguments().end();
//      ait++)
//  {
//    slicing_data[goto_program.instructions.begin()].determined.insert(
//      ait->get("#identifier")); // arguments are always determined.
//  }
  
    
  // first compute successors
  for(goto_programt::instructionst::const_iterator
      it=goto_program.instructions.begin();
      it!=goto_program.instructions.end();
      it++)
  {    
    goto_program.get_successors(it, slicing_data[it].successors);
    queue.push_back(goto_program.instructions.begin()); // every one gets one shot
  }
  
//  for(goto_programt::instructionst::const_iterator
//      it=goto_program.instructions.begin();
//      it!=goto_program.instructions.end();
//      it++)
//  {
//    if(it->is_assert())
//    {
//      find_symbols_sett temp;
//      find_symbols(it->guard, temp);
//      
//      bool local=true;      
//      for(find_symbols_sett::const_iterator git=temp.begin();
//          git!=temp.end();
//          git++)
//        if(!is_local(scope, *git)) local=false;
//      
//      if(local)
//      {
//        // try to discharge?
//      }
//    }
//  }
  
  // fixed-point
  while(!queue.empty())
  {
    goto_programt::const_targett t=queue.front();
    queue.pop_front();
    
    local_slicing_data_entryt &e=slicing_data[t];
    
    if(t->type==ASSIGN) 
    {
      const code_assignt &code = to_code_assign(to_code(t->code));
      
      if(code.lhs().id()=="symbol")
      {
        const irep_idt &ident = code.lhs().get("identifier");
        
        if(is_nondet(code.rhs()))
        {
          
          for(goto_programt::const_targetst::const_iterator
                p_it=e.successors.begin();
              p_it!=e.successors.end();
              p_it++)
          {
            std::pair<std::set<irep_idt>::const_iterator, bool> ret =
              slicing_data[*p_it].nondets.insert(ident);
            
            if(ret.second) // changed
              queue.push_back(*p_it);
          }
        }
        else
        {
          for(goto_programt::const_targetst::const_iterator
                p_it=e.successors.begin();
              p_it!=e.successors.end();
              p_it++)
          {
            if(slicing_data[*p_it].nondets.find(ident)!=
               slicing_data[*p_it].nondets.end())
            {
              slicing_data[*p_it].nondets.erase(ident);
              // changed, put in queue
              queue.push_back(*p_it);
            }
          }
        }
      }
    }
    else if(t->type==ASSUME || 
            t->type==ASSERT || 
            t->type==GOTO || 
            t->type==OTHER)
    {
      find_symbols_sett guard_syms;
      
      if(t->type==OTHER)
        find_symbols(t->code, guard_syms);
      else
        find_symbols(t->guard, guard_syms);
      
      for(goto_programt::const_targetst::const_iterator
              p_it=e.successors.begin();
              p_it!=e.successors.end();
              p_it++)
      {
        for(find_symbols_sett::const_iterator sit = 
              guard_syms.begin();
            sit!=guard_syms.end();
            sit++)
        {
          // this might not be nondet anymore.
          if(slicing_data[*p_it].nondets.find(*sit)!=
             slicing_data[*p_it].nondets.end())
          {
            slicing_data[*p_it].nondets.erase(*sit);
            // changed, put in queue
            queue.push_back(*p_it);
          }
        }
      }
    }
    else 
    {
      // just pass it on.      
      for(goto_programt::const_targetst::const_iterator
            p_it=e.successors.begin();
          p_it!=e.successors.end();
          p_it++)
      {
        for(std::set<irep_idt>::const_iterator dit = 
              slicing_data[t].nondets.begin();
            dit!=slicing_data[t].nondets.end();
            dit++)
        {
          std::pair<std::set<irep_idt>::const_iterator, bool> ret =
            slicing_data[*p_it].nondets.insert(*dit);
          
          if(ret.second) // changed
            queue.push_back(*p_it);
        }
      }
    }
  }
  
  // now remove those instructions that assign nondet to something nondet.
  for(goto_programt::instructionst::iterator
      it=goto_program.instructions.begin();
      it!=goto_program.instructions.end();
      it++)
  {
    if(it->type==ASSIGN) 
    {
      const code_assignt &code = to_code_assign(to_code(it->code));
      
      if(code.lhs().id()=="symbol") // everything else is too complicated.
      {
        const irep_idt &ident = code.lhs().get("identifier");
        
        if(is_nondet(code.rhs()))
        {
          if (slicing_data[it].nondets.find(ident)!=
              slicing_data[it].nondets.end())
          {
            // this was nondet anyways.
            it->make_skip();        
          }
        }
      }      
    }
  }  
}

#if 0
// disabled: no local_variables anymore

/*******************************************************************\

Function: local_variable_slicer

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void local_variable_slicer(
  const std::set<irep_idt> &scope,
  goto_programt &goto_program)
{
//  unsigned usefulness_count = 0;
  
  goto_program.update();
  
  Forall_goto_program_instructions(it, goto_program)
  {
    if(it->type==ASSIGN)
    {
      const code_assignt &code = to_code_assign(to_code(it->code));      
      
      if(code.lhs().id()=="symbol" && // let's keep this simple for now
         is_local(scope, code.lhs().get("identifier")))
      {
        goto_programt::const_targetst queue;
        goto_program.get_successors(it, queue);
        
        const irep_idt &ident=code.lhs().get("identifier");
        
        bool is_used=false;
        
        while(!queue.empty() && !is_used)
        {
          goto_programt::const_targett t=queue.front();
          queue.pop_front();
          
          if(t==goto_program.instructions.end())
            continue;
          
          if(t->type==ASSIGN)
          {
            const code_assignt &other_code = to_code_assign(to_code(t->code));
            
            if(other_code.lhs()==code.lhs())
            {
              continue; // this was a dead end.
            }
            else
            {
              // the symbol might be used as an index on the lhs!
              if(check_for_symbol(t->code, ident))
              {
                is_used=true;
                break;
              }
            }
          }
          else
          {
            if(check_for_symbol(t->code, ident) ||
               check_for_symbol(t->guard, ident))
            {
              is_used=true;
              break;
            }
          }
          
          // Add successors
          goto_programt::const_targetst temp;
          goto_program.get_successors(t, temp);
          
          for(goto_programt::const_targetst::const_iterator t_it=temp.begin();
              t_it!=temp.end();
              t_it++)
            if(find(queue.begin(), queue.end(), *t_it)==queue.end())
              queue.push_back(*t_it);
        }
        
        if(!is_used)
        {
          it->make_skip();
//          it->labels.push_back("SLICED_AWAY");
//          usefulness_count++;
        }
      }
    }
  }
  
//  if (usefulness_count>0)
//    std::cout << "Just sliced away " << usefulness_count << " instructions." << std::endl;
}

#endif

/*******************************************************************\

Function: is_nondet

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool is_nondet(const exprt &expr)
{
  return (expr.id()=="sideeffect" && expr.get("statement")=="nondet");
}

/*******************************************************************\

Function: check_for_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool check_for_symbol(const exprt &expr, const irep_idt &ident)
{
  if(expr.id()=="symbol")
  {
    return (expr.get("identifier")==ident);
  }
  
  forall_operands(it, expr)
    if(check_for_symbol(*it, ident)) return true;
  
  return false;
}
