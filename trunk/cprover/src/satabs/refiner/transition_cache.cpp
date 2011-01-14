/*******************************************************************\

Module: Simulator

Author: Daniel Kroening
    
Date: October 2005

Purpose:

\*******************************************************************/

#include "transition_cache.h"

/*******************************************************************\

Function: transition_cachet::entryt::build

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void transition_cachet::entryt::build(
  const abstract_stept &abstract_state_from,
  const abstract_stept &abstract_state_to)
{
  pc=abstract_state_from.pc->code.concrete_pc;

  // from

  const std::set<unsigned> &from_predicates=
    abstract_state_from.pc->code.transition_relation.from_predicates;

  for(std::set<unsigned>::const_iterator
      it=from_predicates.begin();
      it!=from_predicates.end();
      it++)
    from[*it]=abstract_state_from.predicate_values[*it];

  // to

  const std::set<unsigned> &to_predicates=
    abstract_state_from.pc->code.transition_relation.to_predicates;

  for(std::set<unsigned>::const_iterator
      it=to_predicates.begin();
      it!=to_predicates.end();
      it++)
    to[*it]=abstract_state_to.predicate_values[*it];
}
