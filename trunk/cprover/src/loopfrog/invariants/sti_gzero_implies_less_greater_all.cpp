/*******************************************************************

 Module: A combination of state and transition invariants
         a>=0  => a' >/< a
 Author: Aliaksei Tsitovich

\*******************************************************************/

#include <ansi-c/expr2c.h>
#include <ansi-c/c_types.h>
#include <std_expr.h>
#include <pointer_expr.h>
#include <expr_util.h>
#include <arith_tools.h>
#include <goto-programs/string_abstraction.h>

#include "string_utils.h"

#include "sti_gzero_implies_less_greater_all.h"


/*******************************************************************\
 
 Function: sti_gzero_implies_less_greater_all_invariant_testt::get_invariants

 Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

 void sti_gzero_implies_less_greater_all_invariant_testt::get_transition_invariants(
  const loop_summaryt &summary,
  transition_invariantst &candidates)
{
  namespacet ns( context );

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

      constant_exprt max_expr(it->type());
      constant_exprt min_expr(it->type());

      max_expr.set_value(integer2binary(power(2, atoi(it->type().get(ID_width).c_str())-1)-1, atoi(it->type().get(ID_width).c_str())));
      min_expr.set_value(integer2binary(power(2, atoi(it->type().get(ID_width).c_str())-1), atoi(it->type().get(ID_width).c_str())));

//      std::cout <<"MAX: " <<max_expr << " MIN: " << min_expr<< " of type " << it->type() << std::endl;

      binary_relation_exprt i_le_max( *it, "<", max_expr );
      binary_relation_exprt i_ge_zero( *it, ">=", gen_zero(it->type()) );

      std::set<exprt> assumes;
      assumes.insert(i_le_max);
      assumes.insert(i_ge_zero);

      binary_relation_exprt rel1( *it, ">", temp );
      candidates.push_back( transition_invariantt ( rel1, mapping,  assumes) );

      binary_relation_exprt i_ge_min( *it, ">", min_expr );
      assumes.clear();
      assumes.insert(i_ge_min);
      assumes.insert(i_ge_zero);

      binary_relation_exprt rel2( *it, "<", temp );
      candidates.push_back( transition_invariantt ( rel2, mapping,  i_ge_min) );

#if 0
      std::cout << "REL INVARIANT: " << expr2c(invariant, ns) << std::endl;
#endif
    }
    ++it;
  }

  //  std::set<exprt> indexes;
  //
  //  find_indexes( summary.variant, indexes );
  //  find_indexes( summary.rhs_expressions, indexes );
  //


//  for( std::set<exprt>::const_iterator it = indexes.begin( ); it != indexes.end( ); it++ )
//  {
//
//    const exprt &array = it->op0( );
//    const exprt &index = it->op1( );
//    var_mappingt mapping;
//    exprt temp = get_temporary_symbol( index.type( ) );
//    mapping[index] = temp;
//
//    zero_string_exprt zt( array );
//    binary_relation_exprt i_ge_z( index, ">=", gen_zero( index.type( ) ) );
//    and_exprt precond( zt, i_ge_z );
//
//    binary_relation_exprt rel1( index, ">", temp );
//    implies_exprt invariant1( i_ge_z, rel1 );
//    potential_invariants_and_mappings.insert( make_pair( invariant1, mapping ) );
//
//    binary_relation_exprt rel2( index, "<", temp );
//    implies_exprt invariant2( i_ge_z, rel2 );
//    potential_invariants_and_mappings.insert( make_pair( invariant2, mapping ) );
//  }

}


 /*******************************************************************\

  Function: sti_gzero_implies_less_greater_all_invariant_testt::find_indexes

  Inputs:

  Outputs:

  Purpose:

 \*******************************************************************/

 void sti_gzero_implies_less_greater_all_invariant_testt::find_indexes(
   const exprt &expr,
   std::set<exprt> &to) const
 {
   if(expr.id()=="index")
   {
     const exprt &array = expr.op0();

     if (array.id()=="symbol" ||
         array.id()==ID_string_constant)
     {
       const typet &type = ns.follow(array.type());

       if(type.id()=="array")
         to.insert(expr);
     }
   }
   else
     forall_operands(it, expr)
       find_indexes(*it, to);
 }

 /*******************************************************************\

  Function: sti_gzero_implies_less_greater_all_invariant_testt::find_indexes

  Inputs:

  Outputs:

  Purpose:

 \*******************************************************************/

 void sti_gzero_implies_less_greater_all_invariant_testt::find_indexes(
   const std::set<exprt> &from,
   std::set<exprt> &to) const
 {
   for(std::set<exprt>::const_iterator it=from.begin();
       it!=from.end();
       it++)
   {
     find_indexes(*it, to);
   }
 }
