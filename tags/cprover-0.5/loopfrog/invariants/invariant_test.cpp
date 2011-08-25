/*******************************************************************\

 Module: A string zero-termination invariant

 Author: CM Wintersteiger

\*******************************************************************/

#include <expr_util.h>
#include <i2string.h>

#include "invariant_test.h"

/*******************************************************************\

 Function: invariant_testt::get_temporary_symbol

 Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

symbol_exprt invariant_testt::get_temporary_symbol(const typet &type)
{
  symbolt new_symbol;
  symbolt *symbolp = NULL;

  new_symbol.type = type;

  do
  {
    new_symbol.name=new_symbol.base_name=
        std::string("invariant_test::temporary$") +
        i2string(++temporary_counter);

    context.move(new_symbol, symbolp);
  }
  while(symbolp==NULL);

  return symbol_exprt(symbolp->name, type);
//  return symbol_exprt(symbolp->name, symbolp->type);
}
