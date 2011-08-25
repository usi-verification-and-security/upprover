/*******************************************************************\

Module: Create abstract expression from concrete one

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <assert.h>

#include <i2string.h>
#include <expr_util.h>

#include "abstract_expression.h"
#include "canonicalize.h"
#include "lift_if.h"

/*******************************************************************\

Function: make_it_a_predicate

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void make_it_a_predicate(
  const predicatest &predicates,
  exprt &expr,
  const namespacet &ns)
{
  bool negation;
  canonicalize(expr, negation, ns);

  // see if we have it
  unsigned nr;
  if(predicates.find(expr, nr))
  {
    // yes, we do!

    // see if it is a constant
    if(predicates[nr].is_true())
      expr.make_true();
    else if(predicates[nr].is_false())
      expr.make_false();
    else
    {
      expr=exprt(ID_predicate_symbol, typet(ID_bool));
      expr.set(ID_identifier, nr);
    }

    if(negation)
      expr.make_not();
  }
  else
  {
    // nah, we don't
    // make it nondeterministic choice
    exprt tmp(ID_nondet_symbol, typet(ID_bool));
    tmp.add(ID_expression).swap(expr);
    expr.swap(tmp);
  }
}

/*******************************************************************\

Function: abstract_expression

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void abstract_expression(
  const predicatest &predicates,
  exprt &expr,
  const namespacet &ns)
{
  if(expr.type().id()!=ID_bool)
    throw "abstract_expression expects expression of type Boolean";

  if(expr.id()==ID_and || expr.id()==ID_or ||
     expr.id()==ID_implies || expr.id()==ID_xor)
  {
    Forall_operands(it, expr)
      abstract_expression(predicates, *it, ns);
  }
  else if(expr.id()==ID_not)
  {
    assert(expr.operands().size()==1);

    abstract_expression(predicates, expr.op0(), ns);

    // remove double negation
    if(expr.op0().id()==ID_not &&
       expr.op0().operands().size()==1)
    {
      exprt tmp;
      tmp.swap(expr.op0().op0());
      expr.swap(tmp);
    }
  }
  else if(expr.id()==ID_if)
  {
    assert(expr.operands().size()==3);
  
    Forall_operands(it, expr)
      abstract_expression(predicates, *it, ns);

    exprt true_expr(ID_and, bool_typet());
    true_expr.copy_to_operands(expr.op0(), expr.op1());
    
    exprt false_expr(ID_and, bool_typet());
    false_expr.copy_to_operands(gen_not(expr.op0()), expr.op2());
    
    exprt or_expr(ID_or, bool_typet());
    or_expr.move_to_operands(true_expr, false_expr);
    
    expr.swap(or_expr);
  }
  else if(expr.id()==ID_equal || expr.id()==ID_notequal)
  {
    if(expr.operands().size()!=2)
      throw expr.id_string()+" takes two operands";

    // Is it equality on Booleans?

    if(expr.op0().type().id()==ID_bool &&
       expr.op1().type().id()==ID_bool)
    {
      // leave it in

      Forall_operands(it, expr)
        abstract_expression(predicates, *it, ns);
    }
    else // other types, make it a predicate
    {
      if(has_non_boolean_if(expr))
      {
        lift_if(expr);
        abstract_expression(predicates, expr, ns);
      }
      else
        make_it_a_predicate(predicates, expr, ns);
    }
  }
  else if(expr.is_constant())
  {
    // leave it as is
  }
  else if(has_non_boolean_if(expr))
  {
    lift_if(expr);
    abstract_expression(predicates, expr, ns);
  }
  else
  {
    make_it_a_predicate(predicates, expr, ns);
  }
}
