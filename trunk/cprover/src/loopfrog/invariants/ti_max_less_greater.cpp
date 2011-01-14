/*******************************************************************

 Module: maximum or minimum of all numeric variables is strictly
 	     increasing or decresing
         max(a',b') >/< max(a,b)
         min(a',b') >/< min(a,b)
 Author: Aliaksei Tsitovich

\*******************************************************************/

#include <ansi-c/expr2c.h>
#include <ansi-c/c_types.h>
#include <std_expr.h>
#include <expr_util.h>
#include <goto-programs/string_abstraction.h>
#include <arith_tools.h>

#include "string_utils.h"

#include "ti_max_less_greater.h"


/*******************************************************************\
 
 Function: ti_max_less_greater_invariant_testt::get_transition_invariants

 Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

 void ti_max_less_greater_invariant_testt::get_transition_invariants(
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

    exprt lhs2 = it->first;
    exprt rhs2 = it->second;

    ++it;
    for( ; it != mapping.end( ); ++it )
    {
      if (mapping.begin()->first.type() == it->first.type())
      {
        lhs = if_exprt( binary_relation_exprt(lhs, ID_ge, it->first), lhs, it->first );
        rhs = if_exprt( binary_relation_exprt(rhs, ID_ge, it->first), rhs, it->first );

        lhs2 = if_exprt( binary_relation_exprt(lhs2, ID_le, it->first), lhs2, it->first );
        rhs2 = if_exprt( binary_relation_exprt(rhs2, ID_le, it->first), rhs2, it->first );

      }
    }
    binary_relation_exprt inv1( lhs, ID_gt, rhs );
    binary_relation_exprt inv2( lhs, ID_lt, rhs );
    candidates.push_back( transition_invariantt( inv1, mapping) );
    candidates.push_back( transition_invariantt( inv2, mapping) );

    binary_relation_exprt inv3( lhs2, ID_gt, rhs2 );
    binary_relation_exprt inv4( lhs2, ID_lt, rhs2 );
    candidates.push_back( transition_invariantt( inv3, mapping) );
    candidates.push_back( transition_invariantt( inv4, mapping) );

  }
}
