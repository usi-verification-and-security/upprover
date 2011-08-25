/*******************************************************************

 Module: disjunctive transition invariant of >/< for two branches
         a' >/< a or b' >/< b
 Author: Aliaksei Tsitovich

\*******************************************************************/

#include <ansi-c/expr2c.h>
#include <ansi-c/c_types.h>
#include <std_expr.h>
#include <expr_util.h>
#include <goto-programs/string_abstraction.h>
#include <arith_tools.h>

#include "string_utils.h"

#include "ti_sum_less_greater.h"


/*******************************************************************\
 
 Function: ti_sum_less_greater_invariant_testt::get_transition_invariants

 Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

 void ti_sum_less_greater_invariant_testt::get_transition_invariants(
  const loop_summaryt &summary,
  transition_invariantst &candidates)
{
  namespacet ns(context);

  std::set<exprt> symbols;

  for (std::set<exprt>::const_iterator it=summary.variant.begin();
       it!=summary.variant.end();
       it++)
    find_symbols(*it, symbols);

  or_exprt big_or;
  var_mappingt mapping;

  for( std::set<exprt>::const_iterator it = symbols.begin( ); it != symbols.end( ); ++it )
  {
    if (is_number(it->type( )))
    {
      exprt temp = get_temporary_symbol( it->type( ) );
      mapping[*it] = temp;
    }
  }

  if( mapping.size( ) > 0 )
  {
    var_mappingt::const_iterator it = mapping.begin( );
    exprt lhs = it->first;
    exprt rhs = it->second;
    ++it;
    for( ; it != mapping.end( ); ++it )
    {
      if (mapping.begin()->first.type() == it->first.type())
      {
        lhs = plus_exprt( lhs, it->first );
        rhs = plus_exprt( rhs, it->second );
      }
    }


    binary_relation_exprt inv1( lhs, ID_gt, rhs );
    binary_relation_exprt inv2( lhs, ID_lt, rhs );
    candidates.push_back( transition_invariantt( inv1, mapping) );
    candidates.push_back( transition_invariantt( inv2, mapping) );

  }
}
