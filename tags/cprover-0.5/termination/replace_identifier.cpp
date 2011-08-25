/*******************************************************************\

Module: 

Author: CM Wintersteiger

\*******************************************************************/

#include <std_types.h>

#include "replace_identifier.h"

/********************************************************************\

 Function: replace_idt::replace

 Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

bool replace_idt::replace(exprt &expr) const
{
  if(expr.id()==ID_symbol)
  {
    const_iterator it=find(expr.get(ID_identifier));

    if(it!=end())
    {
      expr.set(ID_identifier, it->second);
      return false;
    }
  }

  bool result=true;

  Forall_operands(it, expr)
    result=replace(*it) && result;

  result=replace(expr.type()) && result;

  return result;
}

/********************************************************************\

 Function: replace_idt::replace

 Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

bool replace_idt::replace(typet &type) const
{
  if(type.has_subtype())
    replace(type.subtype());

  Forall_subtypes(it, type)
    replace(*it);
    
  if(type.id()==ID_struct ||
     type.id()==ID_union)
  {
    struct_typet &struct_type = to_struct_type(type);    
    struct_typet::componentst &components = struct_type.components();
    for (struct_typet::componentst::iterator it = components.begin();
         it!=components.end();
         it++)
      replace(*it);
  } 
  else if(type.id()==ID_code)
  {
    code_typet &code_type=to_code_type(type);
    code_typet::argumentst &arguments=code_type.arguments();
    for (code_typet::argumentst::iterator it = arguments.begin();
         it!=arguments.end();
         it++)
      replace(*it);
  }
  
  if(type.id()==ID_symbol)
  {
    const_iterator it=find(type.get(ID_identifier));

    if(it!=end())
    {
      type.set(ID_identifier, it->second);
      return false;
    }
  }

  return true;
}
