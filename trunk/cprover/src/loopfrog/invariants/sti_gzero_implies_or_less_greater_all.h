/*******************************************************************

 Module: a>=0 and b>=0 => a' >/< a or b' >/< b

 Author: Aliaksei Tsitovich

\*******************************************************************/

#ifndef __CPROVER_LOOPFROG_INVARIANTS_STI_GZERO_IMPLIES_OR_LESS_GREATER_ALL_H_
#define __CPROVER_LOOPFROG_INVARIANTS_STI_GZERO_IMPLIES_OR_LESS_GREATER_ALL_H_

#include "invariant_test.h"

class sti_gzero_implies_or_less_greater_all_invariant_testt :
  public invariant_testt
{
public:
  sti_gzero_implies_or_less_greater_all_invariant_testt(
    contextt &context) : 
      invariant_testt("ST2", ">=0=> >/< or >/<", context, STATE_AND_TRANSITION),
      ns(context) {}
  
  virtual ~sti_gzero_implies_or_less_greater_all_invariant_testt(void) {}
  
  virtual void get_transition_invariants(
    const loop_summaryt &summary,
    transition_invariantst &candidates);
protected:
  const namespacet ns;

};

#endif /*__CPROVER_LOOPFROG_INVARIANTS_STI_GZERO_IMPLIES_OR_LESS_GREATER_ALL_H_*/
