/*******************************************************************\

Module: The Concrete Model

Author: Daniel Kroening

Date: May 2006

\*******************************************************************/

#include "../prepare/concrete_model.h"
#include "../abstractor/abstract_model.h"

void substitute_invariants(
  const concrete_modelt &concrete_model,
  abstract_programt::targett pc,
  exprt &predicate);
