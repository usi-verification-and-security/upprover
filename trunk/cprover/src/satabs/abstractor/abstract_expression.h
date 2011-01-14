/*******************************************************************\

Module: Create abstract expression from concrete one

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_CEGAR_ABSTRACT_EXPRESSION_H
#define CPROVER_CEGAR_ABSTRACT_EXPRESSION_H

#include <namespace.h>

#include "predicates.h"

void abstract_expression(
  const predicatest &predicates,
  exprt &expr,
  const namespacet &ns);

#endif
