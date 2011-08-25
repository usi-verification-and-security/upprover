/*******************************************************************\

Module: Local Variables Helpers

Author: CM Wintersteiger

\*******************************************************************/

#include <find_symbols.h>

#include "local_variables.h"

/*******************************************************************\

Function: is_local

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

bool is_local(
  const std::set<irep_idt> &scope,
  const irep_idt &ident)
{
  const std::string &idstring = ident.as_string();
    
  if(idstring.size()>15 && 
    idstring.substr(idstring.size()-15)=="#is_zero_string")
    return (scope.find(idstring.substr(0,idstring.size()-15))!=scope.end());
  if(idstring.size()>7 && 
    idstring.substr(idstring.size()-7)=="#length") 
    return (scope.find(idstring.substr(0,idstring.size()-7))!=scope.end());
    
  return (scope.find(ident)!=scope.end());
}



void find_locals(
  const goto_programt::const_targett &target,
  const goto_programt::local_variablest &scope,
  std::set<irep_idt> &locals)
{
  find_locals(target->guard, scope, locals);
  find_locals(target->code, scope, locals);
}

void find_locals(
  const exprt &e,
  const goto_programt::local_variablest &scope,
  std::set<irep_idt> &locals)
{
  find_symbols_sett temp;
  find_symbols(e, temp);
  
  for(find_symbols_sett::const_iterator it = temp.begin();
      it!=temp.end();
      it++)
    if(is_local(scope, *it)) locals.insert(*it);
}

bool uses_only_locals(
  const goto_programt::const_targett &target,
  const goto_programt::local_variablest &scope)
{
  find_symbols_sett temp;
  find_symbols(target->guard, temp);
  find_symbols(target->code, temp);
  
  for(find_symbols_sett::const_iterator it = temp.begin();
      it!=temp.end();
      it++)
    if(!is_local(scope, *it)) return false;
  
  return true;
}
