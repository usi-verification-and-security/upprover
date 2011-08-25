/*******************************************************************

 Module: Adaptor for invariant propagation to prove claims in Loopfrog

 Author: A. Tsitovich

\*******************************************************************/

#include <simplify_expr.h>

#include "invariant_propagation_adaptor.h"

/*******************************************************************\

Function: invariant_propagation_adaptort::implies_claim

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool invariant_propagation_adaptort::implies_claim(goto_programt::targett &i_it) const
{
  // find invariant set
  state_mapt::const_iterator s_it=state_map.find(i_it);

  if (s_it==state_map.end())
    return false;

  const invariant_sett &invariant_set=s_it->second.invariant_set;

  exprt simplified_guard(i_it->guard);

  invariant_set.simplify(simplified_guard);
  ::simplify(simplified_guard, ns);

  return invariant_set.implies(simplified_guard).is_true();
}
