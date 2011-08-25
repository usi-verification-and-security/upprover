/*******************************************************************\

 Module: A pointer offset invariant

 Author: CM Wintersteiger

\*******************************************************************/

#ifndef __CPROVER_LOOPFROG_INVARIANTS_POINTER_OFFSET_H_
#define __CPROVER_LOOPFROG_INVARIANTS_POINTER_OFFSET_H_

#include "invariant_test.h"

class pointer_offset_invariant_testt : 
  public invariant_testt
{
public:
  pointer_offset_invariant_testt(
    contextt &context) : 
      invariant_testt("POFF", "Pointer Offset", context) {}
  
  virtual ~pointer_offset_invariant_testt(void) {}
  
  virtual void get_invariants(
    const loop_summaryt &summary,
    std::set<exprt> &potential_invariants);
  
};

#endif /*__CPROVER_LOOPFROG_INVARIANTS_POINTER_OFFSET_H_*/
