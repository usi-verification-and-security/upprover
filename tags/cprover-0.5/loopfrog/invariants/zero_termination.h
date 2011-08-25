/*******************************************************************

 Module: A string zero-termination invariant

 Author: CM Wintersteiger

\*******************************************************************/

#ifndef __CPROVER_LOOPFROG_INVARIANTS_ZERO_TERMINATION_H_
#define __CPROVER_LOOPFROG_INVARIANTS_ZERO_TERMINATION_H_

#include "invariant_test.h"

class zero_termination_invariant_testt : 
  public invariant_testt
{
public:
  zero_termination_invariant_testt(
    contextt &context) : 
      invariant_testt("ZT", "Zero Termination", context) {}
  
  virtual ~zero_termination_invariant_testt(void) {}
  
  virtual void get_invariants(
    const loop_summaryt &summary,
    std::set<exprt> &potential_invariants);
  
};

#endif /*__CPROVER_LOOPFROG_INVARIANTS_ZERO_TERMINATION_H_*/
