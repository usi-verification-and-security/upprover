/*******************************************************************\
 
Module: loop classification for Loopfrog: string class
 
Author: Daniel Kroening
        CM Wintersteiger
 
Date: June 2007
 
\*******************************************************************/

#include <fstream>
#include <std_code.h>
#include <assert.h>

#include <simplify_expr.h>
#include <find_symbols.h>

#include "class_nocharsearch.h"
#include "class_charsearch.h"
#include "string_utils.h"

/*******************************************************************\
 
Function: class_nocharsearcht::class_nocharsearcht
 
  Inputs:
 
 Outputs:
 
 Purpose: 
 
\*******************************************************************/
class_nocharsearcht::class_nocharsearcht(const value_propagation_fivrt &vp) : 
  class_baset(vp)   
{ 
  std::ofstream f("loops_nochar_search", std::ios::out); f.close();
}

/*******************************************************************\
 
Function: class_nocharsearcht::recognize
 
  Inputs:
 
 Outputs:
 
 Purpose: 
 
\*******************************************************************/
bool class_nocharsearcht::recognize( 
  const contextt& context, 
  const goto_programt& program,
  goto_programt::const_targett &begin,
  goto_programt::const_targett &end)
{
  unsigned state=0;
  irep_idt string_pointer_ident("");
  
  goto_programt::const_targett i=begin;
  do
  {
    const value_sett vset;
    
    switch (i->type)
    {
      case NO_INSTRUCTION_TYPE: {
        throw "Unknown instruction type encountered.";
        break; 
      }
      case GOTO: {
        if (state==0 && i==begin &&            
            i->targets.size()==1 &&
            i->targets.front()->location_number > end->location_number &&
            i->guard.id()=="not")
        {
          string_pointer_ident = check_and(i->guard.op0(), true);
          if (string_pointer_ident!="")
            state = 1;
        } 
        else if (state==1)
        {
          if (!(i->targets.size()==1 &&
                i->targets.front()->location_number > i->location_number &&
                i->targets.front()->location_number < end->location_number))
            state=7;
        }        
        else if (state==2 && i==end)
        {
          if (i->guard.is_true() &&
              i->targets.size()==1 &&
              *i->targets.begin()==begin)
            state = 3;
        }
        else
          if (state <=3 ) state=7;          
        break;
      }
      case ASSUME: 
      case ASSERT: 
      case OTHER:
      case RETURN: {
        if (state <=3 ) state=5;                 
        break; 
      }
      case ASSIGN: {
        const code_assignt& code = to_code_assign(to_code(i->code)); 
        const exprt& lhs = code.lhs();
        const exprt& rhs = code.rhs();
        
        if (state==0 || state==1)
        {
          if (lhs.id()=="dereference" || lhs.id()=="index")
          {
            find_symbols_sett syms;
            find_string_type_symbols(lhs.op0(), vset, syms);            
            if (syms.find(string_pointer_ident)!=syms.end())
              state=4;
          } 
          else if (lhs.id()=="symbol")
          { 
            if (state==1 && 
                lhs.get("identifier")==string_pointer_ident &&
                rhs.id()=="+" &&
                rhs.operands().size()==2 &&
                ((rhs.op0().is_one() && rhs.op1()==lhs) ||
                (rhs.op1().is_one() && rhs.op0()==lhs)))
            {
              state=2;
            } 
            else if (state==0 || state==1 || state==2)
            {
              if (lhs.get("identifier")==string_pointer_ident)
                state=4;
            }             
          }          
        } else if (state==3) 
          state=4;          
        break;
      }
      case FUNCTION_CALL: { 
//        const code_function_callt& code = 
//          to_code_function_call(to_code(i->code));
//        const exprt& lhs = code.lhs();        
//        const exprt::operandst& arguments = code.arguments();
//        
//        
//        
//        for(exprt::operandst::const_iterator it=arguments.begin();
//            it!=arguments.end();
//            it++)
//        {
//          
//        }
        if (state <=3 ) state=6;
        break; 
      }
            
      case LOCATION:
      case SYNC:
      case SKIP:
      case END_FUNCTION:
      case ATOMIC_BEGIN: 
      case ATOMIC_END:
      case START_THREAD: 
      case END_THREAD:
      default: break; /* Nothing */
    }
  } while(i++!=end);
  
  if (state==3) 
  {
    save_loop("loops_nochar_search", context, program, begin, end);
    return true;
  }
  
//  std::cout << "ERRORSTATE: " << state << std::endl;
  
//  if (written_strings.size()==1 && read_strings.size()==1)
//  {    
//    std::ofstream f("loops-1-1", std::ios::app);
//    f << "----------------------" << std::endl;
//    namespacet ns(context);
//    goto_programt::const_targett i=begin;
//    do
//    {      
//      program.output_instruction(ns, "", f, i);
//    } while(i++!=end);    
//    f << std::endl;
//    f.close();
//    R1W1loops++;
//  }
  
  return false; // not a string loop
}

/*******************************************************************\
 
Function: class_nocharsearcht::report
 
  Inputs:
 
 Outputs:
 
 Purpose: 
 
\*******************************************************************/
void class_nocharsearcht::report( std::ostream& out )
{
  out << "No-Character Search Loops : " << recognized << std::endl;
}
