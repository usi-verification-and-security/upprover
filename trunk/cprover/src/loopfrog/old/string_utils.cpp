/*******************************************************************\
 
Module: loop classification for Loopfrog: helpers
 
Author: Daniel Kroening
        CM Wintersteiger
 
Date: June 2007
 
\*******************************************************************/

#include <find_symbols.h>

#include "string_utils.h"

/*******************************************************************\
 
Function: find_string_type
 
  Inputs:
 
 Outputs:
 
 Purpose: 
 
\*******************************************************************/
bool find_string_type(const exprt& expr)
{
  if (is_string_type(expr.type()))
    return true;
  else 
    forall_operands(it, expr)
      if (find_string_type(*it)) return true;
    
  return false;
}

bool check_constant_strings(const exprt& expr)
{
  if (expr.id()==ID_string_constant) 
    return true;
  else forall_operands(it, expr)
       if (check_constant_strings(*it)) return true;
  return false;
}

/*******************************************************************\
 
Function: find_string_type_symbols
 
  Inputs:
 
 Outputs:
 
 Purpose: 
 
\*******************************************************************/
bool find_string_type_symbols(
  const exprt& expr, 
  const value_sett& vset,
  find_symbols_sett &syms)
{
  if (is_string_type(expr.type()))
  {    
    find_symbols_with_members(expr, vset, syms);
    if (check_constant_strings(expr))
      syms.insert("CONSTANTS");
  }
  else 
    forall_operands(it, expr)
    {
      find_string_type_symbols(*it, vset, syms);      
    }
    
  return (syms.size()>0);
}

/*******************************************************************\
 
Function: is_string_type
 
  Inputs:
 
 Outputs:
 
 Purpose: 
 
\*******************************************************************/
bool is_string_type(const typet& type)
{
  if (type.id()=="pointer" || 
      type.id()=="array")
      if (is_char_type(type.subtype()))
        return true;
      else return is_string_type(type.subtype());
  else
    return false;
}

/*******************************************************************\
 
Function: is_char_type
 
  Inputs:
 
 Outputs:
 
 Purpose: 
 
\*******************************************************************/
bool is_char_type(const typet& type)
{
  if ((type.id()=="signedbv" ||
      type.id()=="unsignedbv" ) && 
      type.get("width") == "8")
    return true;
  else
    return false;
}

/*******************************************************************\
 
Function: is_int_type
 
  Inputs:
 
 Outputs:
 
 Purpose: 
 
\*******************************************************************/
bool is_int_type(const typet& type)
{
  if ((type.id()=="signedbv" ||
      type.id()=="unsignedbv" ) &&
      (type.get("width") == "16" ||
      type.get("width") == "32" ||
      type.get("width") == "64"))
    return true;
  else
    return false;
}


/*******************************************************************\

Function: find_symbols_with_members

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void find_symbols_with_members(
  const exprt &src,
  const value_sett& vset,
  find_symbols_sett &dest)
{
  if (src.id()=="member") {
    find_symbols_sett t;
    find_symbols_with_members(src.op0(), vset, t);
    irep_idt cn = src.get("component_name"); 
    for (find_symbols_sett::const_iterator it=t.begin();
         it!=t.end();
         it++)
    {
      std::string s = it->as_string();
      s.append("->");
      s.append(cn.as_string());
      dest.insert(irep_idt(s));
    }
  } else if((src.id()=="symbol") ||
     (src.id()=="next_symbol"))
    dest.insert(src.get("identifier"));
  else
  {
    forall_operands(it, src)
      find_symbols_with_members(*it, vset, dest);
  }
}
