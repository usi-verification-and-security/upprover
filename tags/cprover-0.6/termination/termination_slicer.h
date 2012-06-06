/*******************************************************************\

Module: Abstracting slicer for termination checks

Author: CM Wintersteiger

\*******************************************************************/

#ifndef _CPROVER_SATABS_TERMINATION_SLICER_H_
#define _CPROVER_SATABS_TERMINATION_SLICER_H_

#include <goto-programs/goto_functions.h>

bool sliced_abstraction(  // Return value: if false, the abstraction collapsed
                          // because the assertion is not reachable.
  const contextt &context,
  contextt &shadow_context, // to add static objects when replacing mallocs  
  const goto_functionst &src_functions,
  const irep_idt &entry,
  goto_programt::const_targett &to,
  goto_programt::targett &dest_assertion,
  goto_functionst &dest_functions,
  message_handlert &message_handler,
  bool self_loops=true,                 // self-loops replace unreachable 
                                        // locations; when set to false, 
                                        // we assume(false) instead
  bool abstract_loops=true,             // over-approximation of loops
  unsigned dependency_limit=5,          // over-approximation of complex 
                                        // variable values
  bool replace_dynamic_allocation=false // replace malloc() with static objects
  );

#endif
