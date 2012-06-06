/*******************************************************************\

Module: Refiner

Author: Daniel Kroening

Date: December 2005

Purpose: Calculate predicates for predicate abstraction

\*******************************************************************/

#include <simplify_expr.h>

#include "trans_wp.h"

/*******************************************************************\

Function: trans_wpt::wp_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void trans_wpt::wp_rec(exprt &expr)
{
  Forall_operands(it, expr)
    wp_rec(*it);

  if(expr.id()=="symbol")
  {
    const irep_idt &identifier=expr.get("identifier");
    
    const symbolt &symbol=ns.lookup(identifier);
    
    if(symbol.is_macro)
    {
      // it's just a macro
      expr=symbol.value;
      wp_rec(expr);
    }
    else if(symbol.is_statevar)
    {
      next_state_functionst::const_iterator
        it=next_state_functions.find(identifier);
      
      if(it==next_state_functions.end())
      {
        throw "trans_wpt: no next state function for "+
          id2string(identifier);
      }
      else
      {
        // replace!
        expr=it->second;
      }
    }
    else
    {
      // it's an input or so
      throw "trans_wpt: unexpected symbol: "+id2string(identifier);
    }
  }
}

/*******************************************************************\

Function: trans_wpt::wp

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void trans_wpt::wp(exprt &expr)
{
  wp_rec(expr);
  simplify(expr, ns);
}
