/*******************************************************************\

Module: 

Author: CM Wintersteiger

\*******************************************************************/

#include <arith_tools.h>
#include <i2string.h>

#include "ranking_tools.h"
#include "expr2seneschal.h"

/*******************************************************************\

 Function: expr2seneschalt::convert

 Inputs:

 Outputs:

 Purpose:

\********************************************************************/

std::string expr2seneschalt::convert(
  const exprt &e, 
  bool negated, 
  bool bool_context)
{
  std::string res;

  if(e.id()=="symbol")
  {
    if(bool_context)
      return e.get("identifier").as_string() + "=" + ((negated)?"0":"1");
    else
      return e.get("identifier").as_string();
  }
  else if(e.id()=="constant")
  {
    mp_integer mi;
    to_integer(e, mi);
    
    if(bool_context)
    {
      if(mi==0)
        return "false";
      else
        return "true";
    }
    else
      return integer2string(mi);
  }
  else if(e.id()=="=" || e.id()=="notequal" ||
          e.id()=="<" || e.id()==">" ||
          e.id()=="<=" || e.id()==">=")
  {
    assert(e.operands().size()==2);
    std::string op = e.id()=="notequal" ? "!=" : e.id_string();
    
    if(bool_context && negated)
    {
      if(op=="=") op="!=";
      else if(op=="!=") op="=";
      else if(op=="<") op=">=";
      else if(op==">") op="<=";
      else if(op=="<=") op=">";
      else if(op==">=") op="<";
      else throw std::string("Unknown OP:") + op;
    }
    
    if(!bool_context)
    {
      if(op=="=")
        return "equals("+convert(e.op0())+", "+convert(e.op1())+")";
      if(op=="!=")
        return "not(equals("+convert(e.op0())+", "+convert(e.op1())+"))";
      else
        throw (std::string("Missing Arith-1 Function: ") + op);
    }
    else
      return "(" + convert(e.op0()) + " " + op + " " + convert(e.op1())+")";
  }
  else if(e.id()=="not")
  {
    assert(e.operands().size()==1);
    unsigned w=safe_width(e, ns);
    
    if(bool_context || w==1)
      return std::string("(") + convert(e.op0(), !negated, true) + ")";
    else
    {
      std::string res("bitneg"); 

      if(e.type().id()=="unsignedbv" || e.type().id()=="bool")
        res+="U";
      
      res += i2string(w) + "(" + convert(e.op0()) + ")";
      return res;
    }
  }
  else if(e.id()=="if" && bool_context)
  {
    assert(e.operands().size()==3);
        
    return std::string("((") + convert(e.op0(), false, true) + " & " + 
                               convert(e.op1(), negated, true) + ") | (" +
                               convert(e.op0(), true, true) + " & " + 
                               convert(e.op2(), negated, true) + "))";
  }
  else if(e.id()=="+" || e.id()=="-" || e.id()=="*" || 
          e.id()=="/" || e.id()=="mod" ||
          e.id()=="bitand" || e.id()=="bitor" || e.id()=="bitxor")
  {
    assert(e.operands().size()>=2);
    assert(!bool_context);

    unsigned w=safe_width(e, ns);
    std::string op = e.id()=="+"      ? "add" :
                     e.id()=="-"      ? "sub" :
                     e.id()=="*"      ? "mul" :
                     e.id()=="/"      ? "div" :
                     e.id()=="mod"    ? "mod" :
                     e.id()=="bitand" ? "and" : 
                     e.id()=="bitor"  ? "or"  : 
                                        "xor";
    
    if(op=="add" || op=="sub" || op=="mul" || op=="div")
    {
      if(e.type().id()=="unsignedbv" || e.type().id()=="bool")
        op+="U";
    
      op += i2string(w);
    }

    std::string last;   
    forall_operands(it, e)
    {
      if(it==e.operands().begin())
      {
        exprt::operandst::const_iterator last_it = it;
        it++;
        
        last = op + "(" + convert(*last_it, negated) + "," + 
                          convert(*it, negated) + ")";
      }
      else
        last = op + "(" + last + "," + convert(*it, negated) + ")";
    }
    
    return last;
  }
  else if(e.id()=="unary-" || e.id()=="bitnot")
  {
    assert(e.operands().size()==1);
    assert(!bool_context);
    
    std::string op = (e.id()=="unary-") ? "minus" : "bitneg";
    unsigned w=safe_width(e, ns);
    
    return op + 
           ((e.type().id()=="unsignedbv")?"U":"") + i2string(w) +
           "(" + convert(e.op0(), negated) + ")";
  }
  else if(e.id()=="lshr" || e.id()=="shl")
  {
    assert(e.operands().size()==2);
    assert(!bool_context);
    
    unsigned w=safe_width(e, ns);
    
    return std::string("shift") + 
           ((e.type().id()=="unsignedbv")?"U":"") + i2string(w) +
           "(" + convert(e.op0(), negated) + ", " + 
           ((e.id()=="lshr")?"-":"") + convert(e.op1(), negated) + ")";
  }
  else if(e.id()=="and" || e.id()=="or")
  {
    assert(e.operands().size()>=2);
    assert(bool_context);

    std::string res;
    forall_operands(it, e)
    {
      if(it==e.operands().begin())
        res = "(" + convert(*it, negated, true);
      else
        res += ((e.id()=="and")?" & ":" | ") + convert(*it, negated, true);
    }
    return res+")";
  }
  else if(e.id()=="typecast")
  {
    assert(e.operands().size()==1);   
    unsigned w=safe_width(e, ns);
    
    if(bool_context || w==1)
      return convert(e.op0()) + ((negated)?"!":"") + "=0";
    else
    {     
      return std::string("cast") + 
              ((e.type().id()=="unsignedbv" || e.type().id()=="bool")?"U":"") + 
               i2string(w) + "(" + convert(e.op0(), negated, false) + ")";
    }
  }
  else if(e.id()=="seneschal-range")
  {
    assert(e.operands().size()==1);
    return e.type().id_string() + "(" + convert(e.op0(), negated) + ")";
  }
  else
    throw UnhandledException(e);
}
