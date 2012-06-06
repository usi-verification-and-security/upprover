/*******************************************************************\

Module: Predicate Discovery

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <assert.h>

#include <prefix.h>

#include "discover_predicates.h"
#include "lift_if.h"
#include "canonicalize.h"

/*******************************************************************\

Function: has_if

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool has_if(const exprt &expr)
{
  if(expr.id()==ID_if)
    return true;

  forall_operands(it, expr)
    if(has_if(*it)) return true;
  
  return false;
}

/*******************************************************************\

Function: replace_if

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool replace_if(exprt &expr, exprt &cond, bool branch)
{
  if(expr.id()==ID_if)
  {
    assert(expr.operands().size()==3);
    exprt tmp;
    tmp.swap(branch?expr.op1():expr.op2());
    cond.swap(expr.op0());
    expr.swap(tmp);
    return true;
  }

  Forall_operands(it, expr)
    if(replace_if(*it, cond, branch))
      return true;
  
  return false;
}

/*******************************************************************\

Function: lift_if

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void lift_if(
  const exprt &expr,
  exprt &p0,
  exprt &p1,
  exprt &p2)
{
  p1=expr;
  p2=expr;
  
  replace_if(p1, p0, true);
  replace_if(p2, p0, false);
}

/*******************************************************************\

Function: has_nondet_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static bool has_nondet_symbol(const exprt &expr)
{
  if(expr.id()==ID_nondet_symbol) return true;

  forall_operands(it, expr)
    if(has_nondet_symbol(*it)) return true;

  return false;
}

/*******************************************************************\

Function: has_dynamic_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

static bool has_dynamic_symbol(const exprt &expr)
{
  if(expr.id()==ID_symbol)
  {
    if(expr.type().get_bool("#dynamic")) return true;
    if(has_prefix(expr.get_string(ID_identifier), "symex_dynamic::"))
      return true;
  }

  forall_operands(it, expr)
    if(has_dynamic_symbol(*it)) return true;

  return false;
}

/*******************************************************************\

Function: discover_predicates_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void discover_predicates_rec(
  const exprt &expr,
  std::set<predicatet> &predicates,
  bool canonicalized,
  const namespacet &ns)
{
  assert(expr.type().id()==ID_bool);

  if(expr.id()==ID_and || expr.id()==ID_implies ||
     expr.id()==ID_not || expr.id()==ID_or)
  {
    forall_operands(it, expr)
      discover_predicates_rec(*it, predicates, canonicalized, ns);

    return;
  }
  else if(expr.id()==ID_equal || expr.id()==ID_notequal)
  {
    if(expr.operands().size()==2 &&
       expr.op0().type().id()==ID_bool &&
       expr.op1().type().id()==ID_bool)
    {
      discover_predicates_rec(expr.op0(), predicates, canonicalized, ns);
      discover_predicates_rec(expr.op1(), predicates, canonicalized, ns);
      return;
    }
  }
  else if(expr.id()==ID_if)
  {
    if(expr.operands().size()==3 &&
       expr.op0().type().id()==ID_bool)
    {
      discover_predicates_rec(expr.op0(), predicates, canonicalized, ns);
      discover_predicates_rec(expr.op1(), predicates, canonicalized, ns);
      discover_predicates_rec(expr.op2(), predicates, canonicalized, ns);
      return;
    }
  }
  else if(expr.id()==ID_constant)
  {
    // we don't care about Boolean constants
    return;
  }
  else if(expr.id()==ID_AG)
  {
    assert(expr.operands().size()==1);
    discover_predicates_rec(expr.op0(), predicates, canonicalized, ns);
    return;
  }

  if(!canonicalized)
  {
    exprt tmp(expr);
    bool negation;
    canonicalize(tmp, negation, ns);
    discover_predicates_rec(tmp, predicates, true, ns);
  }
  else if(has_non_boolean_if(expr))
  {
    exprt tmp(expr);
    lift_if(tmp);
    // we have to re-canonicalize after lift_if
    discover_predicates_rec(tmp, predicates, false, ns);
  }
  else
  {
    if(!has_nondet_symbol(expr) &&
       !has_dynamic_symbol(expr))
      predicates.insert(expr);
  }
}

/*******************************************************************\

Function: discover_predicates

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void discover_predicates(
  const exprt &expr,
  std::set<predicatet> &predicates,
  const namespacet &ns)
{
  discover_predicates_rec(expr, predicates, false, ns);
}

