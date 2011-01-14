/*******************************************************************

 Module: sum of all numeric variables is strictly
 	     increasing or decresing
         sum(a',b') >/< sum(a,b)
 Author: Aliaksei Tsitovich

\*******************************************************************/

#ifndef __CPROVER_LOOPFROG_INVARIANTS_TI_SUM_LESS_GREATER_H_
#define __CPROVER_LOOPFROG_INVARIANTS_TI_SUM_LESS_GREATER_H_

#include "invariant_test.h"

class ti_sum_less_greater_invariant_testt :
  public invariant_testt
{
public:
  ti_sum_less_greater_invariant_testt(
    contextt &context) : 
      invariant_testt("TI3", "a'+b'>/<a+b", context, TRANSITION),
      ns(context) {}
  
  virtual ~ti_sum_less_greater_invariant_testt(void) {}
  
  virtual void get_transition_invariants(
    const loop_summaryt &summary,
    transition_invariantst &candidates);

protected:
  const namespacet ns;

};

#endif /*__CPROVER_LOOPFROG_INVARIANTS_TI_SUM_LESS_GREATER_H_*/
