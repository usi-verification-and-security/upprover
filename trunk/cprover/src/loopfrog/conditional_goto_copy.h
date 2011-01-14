/*******************************************************************

 Module: Conditional Copies of a GOTO Programs

 Author: CM Wintersteiger

\*******************************************************************/

#ifndef _CPROVER_LOOPFROG_CONDITIONAL_GOTO_COPY
#define _CPROVER_LOOPFROG_CONDITIONAL_GOTO_COPY

#include <goto-programs/goto_program.h>

void conditional_goto_copy(
  const goto_programt &src,
  goto_programt &dest,
  goto_programt::const_targett &last);

#endif
