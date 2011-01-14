/*******************************************************************

 Module: disjunction of all strict order pairs >/< for all varibles
 		 while the other variables are untouched
         (a'>a and b'=b) or...
 Author: Aliaksei Tsitovich

\*******************************************************************/

#include <ansi-c/expr2c.h>
#include <ansi-c/c_types.h>
#include <std_expr.h>
#include <expr_util.h>
#include <goto-programs/string_abstraction.h>
#include <arith_tools.h>

#include "string_utils.h"

#include "ti_or_less_greater_all.h"


/*******************************************************************\
 
 Function: ti_or_less_greater_all_invariant_testt::get_transition_invariants

 Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

 void ti_or_less_greater_all_invariant_testt::get_transition_invariants(
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

  for (var_mappingt::const_iterator it=mapping.begin(); it!=mapping.end(); ++it)
  {
    and_exprt small_and1;
    and_exprt small_and2;
    binary_relation_exprt rel_a1( it->first, ID_gt, it->second );
    binary_relation_exprt rel_a2( it->first, ID_lt, it->second );
    small_and1.move_to_operands(rel_a1);
    small_and2.move_to_operands(rel_a2);

    for (var_mappingt::const_iterator it2=mapping.begin(); it2!=mapping.end(); ++it2)
    {
      if( it == it2 )
        continue;

      binary_relation_exprt eq1( it2->first, ID_equal, it2->second );
      binary_relation_exprt eq2( it2->first, ID_equal, it2->second );

      small_and1.move_to_operands(eq1);
      small_and2.move_to_operands(eq2);

    }

    big_or.move_to_operands(small_and1);
    big_or.move_to_operands(small_and2);

  }
  candidates.push_back( transition_invariantt( big_or, mapping) );
 
}
