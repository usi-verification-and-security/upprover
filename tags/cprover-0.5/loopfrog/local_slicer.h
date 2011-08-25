/*******************************************************************\

Module: Slicing

Author: CM Wintersteiger

\*******************************************************************/

#ifndef CPROVER_LOOPFROG_LOCAL_SLICER_H
#define CPROVER_LOOPFROG_LOCAL_SLICER_H

#include <goto-programs/goto_functions.h>

void nondet_slicer(  
  goto_programt &goto_program);

#if 0
// disabled: no local_variables anymore
void local_variable_slicer(
  const std::set<irep_idt> &scope,
  goto_programt &goto_program);
#endif

// some helpers...

bool is_nondet(const exprt &expr);
bool check_for_symbol(const exprt &expr, const irep_idt &ident);

#endif
