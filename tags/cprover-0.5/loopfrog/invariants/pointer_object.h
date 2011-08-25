/*******************************************************************\

 Module: A pointer object invariant

 Author: CM Wintersteiger

\*******************************************************************/

#ifndef __CPROVER_LOOPFROG_INVARIANTS_POINTER_OBJECT_H_
#define __CPROVER_LOOPFROG_INVARIANTS_POINTER_OBJECT_H_

#include "invariant_test.h"

class pointer_object_invariant_testt : 
  public invariant_testt
{
public:
  pointer_object_invariant_testt(
    contextt &context) : 
      invariant_testt("PO", "Pointer Object", context) {}
  
  virtual ~pointer_object_invariant_testt(void) {}
  
  virtual void get_invariants(
    const loop_summaryt &summary,
    std::set<exprt> &potential_invariants);
  
};

#endif /*__CPROVER_LOOPFROG_INVARIANTS_POINTER_POINTER_OBJECT_H_*/
