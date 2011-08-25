/*******************************************************************

 Module: Dynamic object replacing

 Author: CM Wintersteiger

\*******************************************************************/

#ifndef _CPROVER_LOOPFROG_REPLACE_MALLOC_H_
#define _CPROVER_LOOPFROG_REPLACE_MALLOC_H_

#include <context.h>
#include <goto-programs/goto_functions.h>
#include <pointer-analysis/value_sets.h>

// Warning: This relies on alloc_adaptor being used!

void replace_malloc(
  contextt &context,
  goto_functionst &goto_functions,
  value_setst &value_sets);

#endif /*REPLACE_MALLOC_H_*/
