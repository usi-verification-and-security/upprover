/*******************************************************************

 Module: a>=0 and b>=0 => a' >/< a or b' >/< b

 Author: Aliaksei Tsitovich

\*******************************************************************/

#include <ansi-c/expr2c.h>
#include <ansi-c/c_types.h>
#include <std_expr.h>
#include <expr_util.h>
#include <goto-programs/string_abstraction.h>

#include "string_utils.h"

#include "sti_gzero_implies_or_less_greater_all.h"


/*******************************************************************\
 
 Function: sti_gzero_implies_or_less_greater_all_invariant_testt::get_invariants

 Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

 void sti_gzero_implies_or_less_greater_all_invariant_testt::get_transition_invariants(
  const loop_summaryt &summary,
  transition_invariantst &candidates)
{
//  namespacet ns(context);
//
//  std::set<exprt> symbols;
//
//  for (std::set<exprt>::const_iterator it=summary.variant.begin();
//       it!=summary.variant.end();
//       it++)
//    find_symbols(*it, symbols);
//
//  std::set<exprt>::const_iterator ait = symbols.begin( );
//  std::set<exprt>::const_iterator bit = symbols.begin( );
//  bit++;
//
//  while( ait != symbols.end( ) && bit != symbols.end( ) )
//  {
//    if( *ait != *bit && ait->type( ) == bit->type( ) )
//    {
//      var_mappingt mapping;
//      exprt temp1 = get_temporary_symbol( ait->type( ) );
//      exprt temp2 = get_temporary_symbol( bit->type( ) );
//
//      mapping[*ait] = temp1;
//      mapping[*bit] = temp2;
//
//      binary_relation_exprt rel_a1( *ait, ">", temp1 );
//      binary_relation_exprt rel_a2( *ait, "<", temp1 );
//      binary_relation_exprt rel_b1( *bit, ">", temp2 );
//      binary_relation_exprt rel_b2( *bit, "<", temp2 );
//
//      or_exprt or1( rel_a1, rel_b1 );
//      or_exprt or2( rel_a1, rel_b2 );
//      or_exprt or3( rel_a2, rel_b1 );
//      or_exprt or4( rel_a2, rel_b2 );
//
//      binary_relation_exprt a_ge_z( *ait, ">=", gen_zero( ait->type( ) ) );
//      binary_relation_exprt b_ge_z( *bit, ">=", gen_zero( bit->type( ) ) );
//      and_exprt and1( a_ge_z, b_ge_z );
//
//      implies_exprt implies1( and1, or1 );
//      implies_exprt implies2( and1, or2 );
//      implies_exprt implies3( and1, or3 );
//      implies_exprt implies4( and1, or4 );
//      potential_invariants_and_mappings.insert( make_pair( implies1, mapping ) );
//      potential_invariants_and_mappings.insert( make_pair( implies2, mapping ) );
//      potential_invariants_and_mappings.insert( make_pair( implies3, mapping ) );
//      potential_invariants_and_mappings.insert( make_pair( implies4, mapping ) );
//
//    }
//
//    bit++;
//
//    if( bit == symbols.end( ) )
//    {
//      bit = ++ait;
//      bit++;
//    }
//  }
}
