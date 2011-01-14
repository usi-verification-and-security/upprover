/*******************************************************************

 Module: An iterator is positive invariant

 Author: Aliaksei Tsitovich
         CM Wintersteiger

\*******************************************************************/

#include <ansi-c/expr2c.h>
#include <ansi-c/c_types.h>
#include <std_expr.h>
#include <expr_util.h>

#include "string_utils.h"
#include "pointer_expr.h"

#include "iterator_bounds2.h"

/*******************************************************************\

 Function: iterator_bounds2_invariant_testt::find_indexes

 Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void iterator_bounds2_invariant_testt::find_indexes(
  const exprt &expr,
  std::set<exprt> &to) const
{
  if(expr.id()=="index")
    to.insert(expr);
  else
    forall_operands(it, expr)
      find_indexes(*it, to);
}

/*******************************************************************\

 Function: iterator_bounds2_invariant_testt::find_indexes

 Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void iterator_bounds2_invariant_testt::find_indexes(
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

/*******************************************************************\

 Function: iterator_bounds2_invariant_testt::get_invariants

 Inputs:

 Outputs:

 Purpose: Tests for iterator bounds

\*******************************************************************/

void iterator_bounds2_invariant_testt::get_invariants(
  const loop_summaryt &summary,
  std::set<exprt> &potential_invariants)
{
  std::set<exprt> indexes;

  find_indexes(summary.variant, indexes);
  find_indexes(summary.rhs_expressions, indexes);

 // if(indexes.size()>3) return; // give up on big loops

  // test the invariant for every index and it's iterator
  for(std::set<exprt>::const_iterator it = indexes.begin();
      it!=indexes.end();
      it++)
  {
    #if 0
    std::cout << "IB TEST: " << expr2c(*it, ns) << std::endl;
    #endif

    const index_exprt index_e = to_index_expr(*it);
    const exprt index = index_e.index();
    const typet index_type = ns.follow(index.type());

    binary_relation_exprt invariant(gen_zero(index.type()), "<=", index);

    potential_invariants.insert(invariant);

    #if 0
    std::cout << "IB INVARIANT: " << expr2c(invariant, ns) << std::endl;
    #endif
  }
}
