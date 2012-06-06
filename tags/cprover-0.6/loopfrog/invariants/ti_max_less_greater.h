/*******************************************************************

 Module: maximum or minimum of all numeric variables is strictly
 	     increasing or decresing
         max(a',b') >/< max(a,b)
         min(a',b') >/< min(a,b)
 Author: Aliaksei Tsitovich

\*******************************************************************/

#ifndef __CPROVER_LOOPFROG_INVARIANTS_TI_MAX_LESS_GREATER_H_
#define __CPROVER_LOOPFROG_INVARIANTS_TI_MAX_LESS_GREATER_H_

#include "invariant_test.h"

class ti_max_less_greater_invariant_testt :
  public invariant_testt
{
public:
  ti_max_less_greater_invariant_testt(
    contextt &context) : 
      invariant_testt("TI4", "max(a',b')>/<max(a,b)", context, TRANSITION),
      ns(context) {}
  
  virtual ~ti_max_less_greater_invariant_testt(void) {}
  
  virtual void get_transition_invariants(
    const loop_summaryt &summary,
    transition_invariantst &candidates);

protected:
  const namespacet ns;

};

#endif /*__CPROVER_LOOPFROG_INVARIANTS_TI_MAX_LESS_GREATER_H_*/
