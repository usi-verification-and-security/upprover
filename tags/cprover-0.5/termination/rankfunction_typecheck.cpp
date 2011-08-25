/*******************************************************************\

Module: Custom bitvector-rankfunction typechecker

Author: CM Wintersteiger

Date: May 2009

\*******************************************************************/

#include <std_expr.h>
#include <std_types.h>
#include <arith_tools.h>
#include <config.h>

#include <ansi-c/ansi_c_parser.h>
#include <ansi-c/ansi_c_convert.h>

#include "ranking_tools.h"

#include "rankfunction_typecheck.h"

/*******************************************************************\

 Function: parse_rank_function

 Inputs:

 Outputs:

 Purpose:

\********************************************************************/

bool parse_rank_function(const std::string &code, contextt &context,
                         const namespacet &ext_ns, message_handlert &mh, exprt &rf)
{
  std::stringstream str(code);
  ansi_c_parser.clear();
  ansi_c_parser.filename="";
  ansi_c_parser.in=&str;
  ansi_c_parser.set_message_handler(mh);
  ansi_c_parser.grammar=ansi_c_parsert::EXPRESSION;
  ansi_c_parser.mode=ansi_c_parsert::GCC;
  ansi_c_scanner_init();

  bool result=ansi_c_parser.parse();

  if(ansi_c_parser.parse_tree.items.empty())
    result=true;
  else
  {
    rf.swap(ansi_c_parser.parse_tree.items.front());

    result=ansi_c_convert(rf, "", mh);

    // typecheck it
    if(!result)
    {
      ansi_c_parse_treet ansi_c_parse_tree;
      rankfunction_typecheckt typecheck(ansi_c_parse_tree, context, ext_ns, mh);

      try
      {
        typecheck.typecheck_expr(rf);
      }

      catch(int e)
      {
        typecheck.error();
      }

      catch(const char *e)
      {
        typecheck.error(e);
      }

      catch(const std::string &e)
      {
        typecheck.error(e);
      }

      result=typecheck.get_error_found();
    }
  }


  // save some memory
  ansi_c_parser.clear();

  return result;
}

/********************************************************************\

 Function: rankfunction_typecheckt::typecheck_expr

 Inputs:

 Outputs:

 Purpose:

\********************************************************************/

void rankfunction_typecheckt::typecheck_expr(exprt &expr)
{  
//  std::cout << "CHECKING: " << expr.to_string() << std::endl;

  if(expr.type().id()!="" && expr.type().id()!="integer") return;

  Forall_operands(it, expr)
  {
    typecheck_expr(*it);
    assert(it->type().id()!="");
  }

  if(expr.id()=="symbol")
  {
    const irep_idt &ident = expr.get("identifier");
    const symbolt &symbol = ns.lookup(ident);
    expr.type() = symbol.type;
    
    if(expr.type().id()=="pointer")
    {
      typecast_exprt tc(unsignedbv_typet(config.ansi_c.pointer_width));
      tc.op() = expr;
      expr = tc;
    }
    else if(expr.type().id()=="bool")
    {
      typecast_exprt tc(unsignedbv_typet(1));
      tc.op() = expr;
      expr = tc;
    }  
  }
  else if(expr.id()=="constant")
  {
    if(expr.type().id()=="integer")
    {
      mp_integer ov = string2integer(expr.get("value").as_string());
      mp_integer v = (ov<0)? -ov:ov;

      // how many bits do we need?
      mp_integer c=1;
      unsigned i=1;
      while(c<=v)
      {
        c*=2;
        i+=1;
      }

      expr.type() = signedbv_typet(i+1);
      expr.set("value", integer2binary(ov, i+1));
    }

    assert(expr.type().id()=="unsignedbv" || expr.type().id()=="signedbv");
  }
  else if(expr.id()=="*")
  {
    unsigned total_width=0;

    forall_operands(it, expr)
    {
      typet type=ext_ns.follow(it->type());

      if(type.id()=="unsignedbv")
        total_width += safe_width(*it, ext_ns) + 1; // account for the extra sign bit.
      else if(type.id()=="signedbv")
        total_width += safe_width(*it, ext_ns);
      else if(type.id()=="pointer")
        total_width += config.ansi_c.pointer_width;
      else if(type.id()=="struct" || type.id()=="union" || type.id()=="c_enum")
        total_width += safe_width(*it, ext_ns);
      else if(type.id()=="fixedbv")
        total_width += safe_width(*it, ext_ns) + 1;
      else
        throw std::string("Unhandled Type: ") + it->type().to_string();
    }

    typet ttype=signedbv_typet(total_width);
    typecast_exprt tc(ttype);

    exprt::operandst operands;
    forall_operands(it, expr)
    {
      operands.push_back(tc);
      operands.back().op0() = *it;
    }
    expr.operands() = operands;
    expr.type() = ttype;
  }
  else if(expr.id()=="-" || expr.id()=="+")
  {
    unsigned largest=0;

    forall_operands(it, expr)
    {
      if(it->type().id()=="unsignedbv" ||
         it->type().id()=="signedbv")
        largest = std::max(safe_width(*it, ext_ns), largest);
      else
        throw std::string("Unhandled Type: ") + it->type().to_string();
    }

    typet ttype=signedbv_typet(largest+expr.operands().size());
    typecast_exprt tc(ttype);

    exprt::operandst operands;
    forall_operands(it, expr)
    {
      operands.push_back(tc);
      operands.back().op0() = *it;
    }
    expr.operands() = operands;
    expr.type() = ttype;
  }
  else if(expr.id()=="/")
  {
    assert(expr.operands().size()==2);
    expr.type()==expr.op0().type();
    typecast_exprt tc(expr.op0().type());
    tc.op() = expr.op1();
    expr.op1()=tc;
  }
  else if(expr.id()=="unary-")
  {
    assert(expr.operands().size()==1);
    assert(expr.op0().type().id()=="signedbv");
    expr.type() = expr.op0().type();
  }
  else if(expr.id()=="mod")
  {
    assert(expr.operands().size()==2);
    expr.type() = expr.op1().type();
    typecast_exprt tc(expr.op1().type());
    tc.op() = expr.op0();
    expr.op0()=tc;
  }
  else
    throw std::string("NYI: ") + expr.id_string();
}
