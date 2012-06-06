/*******************************************************************\

 Module: Adaptor for value sets (duplication)

 Author: CM Wintersteiger

\*******************************************************************/

#include <std_expr.h>
#include <std_types.h>
#include <arith_tools.h>
#include <i2string.h>

#include "value_set_duplication_adaptor.h"

void value_set_duplication_adaptort::get_values(
  goto_programt::const_targett l,
  const exprt &expr,
  valuest &dest)
{  
  duplicationt::const_iterator d_it = duplication.find(l);
  if(d_it!=duplication.end())
    get_values(d_it->second, expr, dest);
  else    
    value_sets.get_values(l, expr, dest);
}
