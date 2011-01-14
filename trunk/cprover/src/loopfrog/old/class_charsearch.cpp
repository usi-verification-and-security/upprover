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

#include "class_charsearch.h"
#include "string_utils.h"

/*******************************************************************\
 
Function: class_charsearcht::class_charsearcht
 
  Inputs:
 
 Outputs:
 
 Purpose: 
 
\*******************************************************************/
class_charsearcht::class_charsearcht(const value_propagation_fivrt &vp) : 
  class_baset(vp)   
{ 
  std::ofstream f("loops_char_search", std::ios::out); f.close(); 
}

/*******************************************************************\
 
Function: class_charsearcht::recognize
 
  Inputs:
 
 Outputs:
 
 Purpose: 
 
\*******************************************************************/
bool class_charsearcht::recognize( 
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
          string_pointer_ident = check_and(i->guard.op0());
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
    save_loop("loops_char_search", context, program, begin, end); 
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
 
Function: class_charsearcht::report
 
  Inputs:
 
 Outputs:
 
 Purpose: 
 
\*******************************************************************/
void class_charsearcht::report( std::ostream& out )
{
  out << "Character Search Loops : " << recognized << std::endl;
}

/*******************************************************************\
 
Function: check_and
 
  Inputs:
 
 Outputs:
 
 Purpose: 
 
\*******************************************************************/
irep_idt check_and( const exprt &expr, bool negated )
{
  std::set<exprt> seen_strings;
  std::set<exprt> seen_iterators;
  bool b = check_and_rec(expr, negated, seen_strings, seen_iterators);
  if (!b) return "";
  
  if (seen_strings.size()>1) return "";
  
  for (std::set<exprt>::const_iterator it=seen_strings.begin();
       it!=seen_strings.end();
       it++)
    if (it->id()=="index") std::cout << *it << std::endl;
  
//  for (std::set<exprt>::const_iterator it=seen_iterators.begin();
//       it!=seen_iterators.end();
//       it++)
//    std::cout << *it << std::endl;  
  
  if (seen_strings.size()==1 && seen_iterators.size()==0)
  {  
    if (seen_strings.begin()->id()=="dereference" &&
        seen_strings.begin()->op0().id()=="symbol" &&
        is_string_type(seen_strings.begin()->op0().type()))
      return seen_strings.begin()->op0().get("identifier");
//    else
//      std::cout << *seen_strings.begin() << std::endl;
  }  
  
  return "";
}

/*******************************************************************\
 
Function: check_and_rec
 
  Inputs:
 
 Outputs:
 
 Purpose: 
 
\*******************************************************************/
bool check_and_rec( 
  const exprt &expr, 
  bool negated,
  std::set<exprt> &seen_strings, 
  std::set<exprt> &seen_iterators) 
{
  if (expr.id()=="and")
  {
    if (negated) return false;
    
    forall_operands(it, expr)
      if (!check_and_rec(*it, false, seen_strings, seen_iterators)) return false;
      
    return true;
  }
  else if (expr.id()=="not")
  {
    assert(expr.operands().size()==1);
    return check_and_rec(expr.op0(), !negated, seen_strings, seen_iterators);
  }
  else if (expr.id()=="or")
  {
    if (!negated) return false;
    
    forall_operands(it, expr)
      if (!check_and_rec(*it, false, seen_strings, seen_iterators)) return false;
      
    return true;
  }
  else if (expr.id()=="typecast")
  {
    return check_and_rec(expr.op0(), negated, seen_strings, seen_iterators);
  }
  else if (expr.id()=="dereference")
  {
    if (expr.op0().id()=="symbol")
    {
      seen_strings.insert(expr);
      return true;
    }
    else
      return false;
  }  
  else 
  { 
    exprt tmp(expr);
    simplify(tmp);
  
    if (expr.id()=="notequal")
    {
      if (negated) return false;
      
      if (tmp.operands().size()==2)
      {
        if (tmp.op0().is_constant())
          seen_strings.insert(tmp.op1());
        else if (tmp.op1().is_constant())
          seen_strings.insert(tmp.op0());
        else
          return false;
      }
      else 
        return false;
    }
    else if (expr.id()=="equal")
    {
      if (!negated) return false;
      std::cout << "=" << std::endl;
      if(tmp.operands().size()==2)
      {
        if (tmp.op0().is_constant())
          seen_strings.insert(tmp.op1());
        else if (tmp.op1().is_constant())
          seen_strings.insert(tmp.op0());
        else
          return false;
      } else
        return false;
    }
    else if (tmp.id()=="<")
    {
      if (negated) return false;
      
      assert(tmp.operands().size()==2);
      
      if (tmp.op1().is_constant())
        seen_iterators.insert(tmp.op0());
      else
        return false;
    }
    else if (tmp.id()==">")
    {
      if (negated) return false;
      
      assert(tmp.operands().size()==2);
      
      if (tmp.op0().is_constant())
        seen_iterators.insert(tmp.op1());
      else
        return false;
    }
    else 
      return false;
  }
    
  return true;  
}
