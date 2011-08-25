/*******************************************************************\

Module: Local Variables Helpers

Author: CM Wintersteiger

\*******************************************************************/

#ifndef LOCAL_VARIABLES_H_
#define LOCAL_VARIABLES_H_

#include <irep.h>
#include <goto-programs/goto_program.h>

bool is_local(
  const std::set<irep_idt> &scope,
  const irep_idt &ident);

void find_locals(
  const goto_programt::const_targett &target,
  const goto_programt::local_variablest &scope,
  std::set<irep_idt> &locals);

void find_locals(
  const exprt &e,
  const goto_programt::local_variablest &scope,
  std::set<irep_idt> &locals);

bool uses_only_locals(
  const goto_programt::const_targett &target,
  const goto_programt::local_variablest &scope);

#endif /*LOCAL_VARIABLES_H_*/
