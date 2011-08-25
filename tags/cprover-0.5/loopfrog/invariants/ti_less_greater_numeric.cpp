/*******************************************************************

 Module: Simple transition invariant > or < for int or uint types
         a' >/< a
 Author: Aliaksei Tsitovich

\*******************************************************************/

#include <ansi-c/expr2c.h>
#include <ansi-c/c_types.h>
#include <std_expr.h>
#include <expr_util.h>
#include <goto-programs/string_abstraction.h>

#include "string_utils.h"

#include "ti_less_greater_numeric.h"


/*******************************************************************\
 
 Function: ti_less_greater_numeric_invariant_testt::get_invariants

 Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

 void ti_less_greater_numeric_invariant_testt::get_transition_invariants(
  const loop_summaryt &summary,
  transition_invariantst &candidates)
{
  namespacet ns(context);

  std::set<exprt> symbols;

  for (std::set<exprt>::const_iterator it=summary.variant.begin();
       it!=summary.variant.end();
       it++)
    find_symbols(*it, symbols);

  std::set<exprt>::const_iterator it = symbols.begin( );
  while( it != symbols.end( ) )
  {
    if( is_number(it->type( )))
    {
      var_mappingt mapping;
      exprt temp = get_temporary_symbol( it->type() );
      mapping[*it] = temp;

      binary_relation_exprt invariant1( *it, ">", temp );
      candidates.push_back( transition_invariantt( invariant1, mapping ) );
      binary_relation_exprt invariant2( *it, "<", temp );
      candidates.push_back( transition_invariantt( invariant2, mapping ) );

#if 0
      std::cout << "REL INVARIANT: " << expr2c(invariant, ns) << std::endl;
#endif
    }
    ++it;
  }
}
