/*******************************************************************\

Module: The concrete program

Author: Daniel Kroening

Date: February 2006

\*******************************************************************/

#include "../prepare/concrete_model.h"
#include "../abstractor/predicates.h"

#include "add_invariants.h"

/*******************************************************************\

Function: add_invariants

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void add_invariants(
  const concrete_modelt &concrete_model,
  abstract_programt::targett pc,
  const predicatest &predicates)
{
  #if 0
  // see if an invariant is also a predicate
  const invariant_sett::invariantst &invariants=
    concrete_model.invariant_propagation.lookup(pc->code.concrete_pc).invariants;
  
  for(invariant_sett::invariantst::expr_sett::const_iterator
      it=invariants.expr_set().begin();
      it!=invariants.expr_set().end();
      it++)
  {
    unsigned nr;
    if(predicates.find(*it, nr))
    {
      pc->code.transition_relation.from_predicates.insert(nr);
      pc->code.transition_relation.to_predicates.insert(nr);
    }
  }
  #endif
}
