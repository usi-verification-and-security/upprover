/*******************************************************************

 Module: Simple transition invariant > or < for int or uint types
         a' >/< a
 Author: Aliaksei Tsitovich

\*******************************************************************/

#ifndef __CPROVER_LOOPFROG_INVARIANTS_TI_LESS_GREATER_NUMERIC_H_
#define __CPROVER_LOOPFROG_INVARIANTS_TI_LESS_GREATER_NUMERIC_H_

#include "invariant_test.h"

class ti_less_greater_numeric_invariant_testt :
  public invariant_testt
{
public:
  ti_less_greater_numeric_invariant_testt(
    contextt &context) : 
      invariant_testt("TI1", "num' >/< num", context, TRANSITION),
      ns(context) {}
  
  virtual ~ti_less_greater_numeric_invariant_testt(void) {}
  
  virtual void get_transition_invariants(
    const loop_summaryt &summary,
    transition_invariantst &candidates);

protected:
  const namespacet ns;

};

#endif /*__CPROVER_LOOPFROG_INVARIANTS_TI_LESS_GREATER_NUMERIC_H_*/
