/*******************************************************************\

Module: 

Author: CM Wintersteiger

\*******************************************************************/

#include <std_expr.h>

#include "find_symbols_rw.h"

/********************************************************************\

 Function: find_symbols_w

 Inputs:

 Outputs:

 Purpose:  

\********************************************************************/

void find_symbols_w(
  const exprt& lhs, 
  find_symbols_sett &l)
{
  if(lhs.id()=="symbol")
  {
    l.insert(lhs.get("identifier"));    
  }
  else if(lhs.id()=="index")
  {
    const index_exprt &ie=to_index_expr(lhs);
    find_symbols_w(ie.array(), l);
  }
  else
    forall_operands(it, lhs)
      find_symbols_w(*it, l);
}

/********************************************************************\

 Function: find_symbols_w

 Inputs:

 Outputs:

 Purpose:  

\********************************************************************/

void find_symbols_w(
  const exprt& lhs, 
  std::set<exprt> &l)
{
  if(lhs.id()=="symbol")
  {
    l.insert(lhs);    
  }
  else if(lhs.id()=="index")
  {
    const index_exprt &ie=to_index_expr(lhs);
    find_symbols_w(ie.array(), l);
  }
  else
    forall_operands(it, lhs)
      find_symbols_w(*it, l);
}

/********************************************************************\

 Function: find_symbols_rw

 Inputs:

 Outputs:

 Purpose:  

\********************************************************************/
    
void find_symbols_rw(
  const exprt& expr, 
  find_symbols_sett &l, 
  find_symbols_sett &r)
{
  if(expr.id()=="symbol")
  {
    l.insert(expr.get("identifier"));
  }
  else if(expr.id()=="index")
  {
    const index_exprt &ie=to_index_expr(expr);
    find_symbols_rw(ie.array(), r, l);
    find_symbols(ie.index(), r);
  }
  else
    forall_operands(it, expr)
      find_symbols_rw(*it, l, r);
}

/********************************************************************\

 Function: find_symbols_rw

 Inputs:

 Outputs:

 Purpose:  

\********************************************************************/
    
void find_symbols_rw(
  const exprt& lhs, 
  const exprt& rhs,
  find_symbols_sett &l, 
  find_symbols_sett &r)
{
  find_symbols_rw(lhs, l, r);
  find_symbols(rhs, r);
}

/********************************************************************\

 Function: is_subset

 Inputs:

 Outputs:

 Purpose:  

\********************************************************************/

bool is_subset( // true if l is a subset of r
  const find_symbols_sett &l,
  const find_symbols_sett &r)
{  
  for(find_symbols_sett::const_iterator it=l.begin();
      it!=l.end();
      it++)
    if(r.find(*it)==r.end()) 
      return false;
  
  return true;
}
