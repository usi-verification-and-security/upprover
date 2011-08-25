/*******************************************************************\

Module: Predicate Discovery

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_CEGAR_DISCOVER_PREDICATES_H
#define CPROVER_CEGAR_DISCOVER_PREDICATES_H

#include <set>

#include <namespace.h>

#include "predicates.h"

void discover_predicates(
  const exprt &expr,
  std::set<predicatet> &predicates,
  const namespacet &ns);

#endif
