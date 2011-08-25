/*******************************************************************\

 Module: A string length invariant

 Author: CM Wintersteiger

\*******************************************************************/

#ifndef __CPROVER_LOOPFROG_INVARIANTS_DECREASING_LENGTH_H_
#define __CPROVER_LOOPFROG_INVARIANTS_DECREASING_LENGTH_H_

#include "invariant_test.h"

class decreasing_length_invariant_testt : 
  public invariant_testt
{
public:
  decreasing_length_invariant_testt(
    contextt &context) : 
      invariant_testt("DL", "Decreasing Length", context) {}
  
  virtual ~decreasing_length_invariant_testt(void) {}
  
  virtual void get_invariants(
    const loop_summaryt &summary,
    std::set<exprt> &potential_invariants);
  
};

#endif /*__CPROVER_LOOPFROG_INVARIANTS_DECREASING_LENGTH_H_*/
