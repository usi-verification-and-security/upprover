/*******************************************************************\

Module: The Concrete Model

Author: Daniel Kroening

Date: June 2003

\*******************************************************************/

#ifndef CPROVER_CEGAR_CONCRETE_MODEL_H
#define CPROVER_CEGAR_CONCRETE_MODEL_H

#include <goto-programs/goto_functions.h>

class concrete_modelt
{
public:
  // the namespace
  const namespacet &ns;
  
  // the program
  const goto_functionst &goto_functions;
  
  concrete_modelt(
    const namespacet &_ns,
    const goto_functionst &_goto_functions):
    ns(_ns),
    goto_functions(_goto_functions)
  {
  }
};

#endif
