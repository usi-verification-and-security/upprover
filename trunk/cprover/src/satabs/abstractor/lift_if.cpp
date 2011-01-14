/*******************************************************************\

Module: Predicate Discovery

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <std_types.h>

#include "lift_if.h"

/*******************************************************************\

Function: has_non_boolean_if

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool has_non_boolean_if(const exprt &expr, exprt &cond)
{
  if(expr.id()==ID_if &&
     expr.type().id()!=ID_bool)
  {
    assert(expr.operands().size()==3);
    cond=expr.op0();
    return true;
  }

  forall_operands(it, expr)
    if(has_non_boolean_if(*it, cond))
      return true;
  
  return false;
}

/*******************************************************************\

Function: has_non_boolean_if

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool has_non_boolean_if(const exprt &expr)
{
  exprt cond;
  return has_non_boolean_if(expr, cond);
}

/*******************************************************************\

Function: replace_if

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool replace_if(const exprt &cond, bool branch, exprt &expr)
{
  if(expr.id()==ID_if)
  {
    assert(expr.operands().size()==3);
    
    if(expr.op0()==cond)
    {
      exprt tmp;
      tmp=branch?expr.op1():expr.op2();
      expr.swap(tmp);
      return true;
    }
  }

  Forall_operands(it, expr)
    if(replace_if(cond, branch, *it))
      return true;
  
  return false;
}

/*******************************************************************\

Function: lift_if

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void lift_if(exprt &expr)
{
  exprt cond;
  
  if(has_non_boolean_if(expr, cond))
  {
    exprt new_expr(ID_if, bool_typet());
    new_expr.operands().resize(3);
    new_expr.op0()=cond;
    new_expr.op1()=expr;
    new_expr.op2()=expr;
    replace_if(cond, true, new_expr.op1());
    replace_if(cond, false, new_expr.op2());
    expr=new_expr;
  }
}
