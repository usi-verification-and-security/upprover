/*******************************************************************\

 Module: A string tracker invariant

 Author: CM Wintersteiger

\*******************************************************************/

#ifndef __CPROVER_LOOPFROG_INVARIANTS_CONSTANT_TRACKER_H_
#define __CPROVER_LOOPFROG_INVARIANTS_CONSTANT_TRACKER_H_

#include "invariant_test.h"

class constant_tracker_invariant_testt : 
  public invariant_testt
{
public:
  constant_tracker_invariant_testt(
    contextt &context) : 
      invariant_testt("CT", "Constant Tracker", context) {}
  
  virtual ~constant_tracker_invariant_testt(void) {}
  
  virtual void get_invariants(
    const loop_summaryt &summary,
    std::set<exprt> &potential_invariants);
  
};

#endif /*__CPROVER_LOOPFROG_INVARIANTS_CONSTANT_TRACKER_H_*/

