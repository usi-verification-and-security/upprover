/*******************************************************************

 Module: A (non-)NULL pointer invariant

 Author: CM Wintersteiger

\*******************************************************************/

#ifndef __CPROVER_LOOPFROG_INVARIANTS_NULL_POINTER_H_
#define __CPROVER_LOOPFROG_INVARIANTS_NULL_POINTER_H_

#include "invariant_test.h"

class null_pointer_invariant_testt : 
  public invariant_testt
{
public:
  null_pointer_invariant_testt(
    contextt &context) : 
      invariant_testt("NP", "NULL-Pointer", context) {}
  
  virtual ~null_pointer_invariant_testt(void) {}
  
  virtual void get_invariants(
    const loop_summaryt &summary,
    std::set<exprt> &potential_invariants);
  
};

#endif /*__CPROVER_LOOPFROG_INVARIANTS_NULL_POINTER_H_*/
