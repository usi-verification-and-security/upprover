/*******************************************************************

 Module: Simple transition invariant > or < for all variables
         a' >/< a
 Author: Aliaksei Tsitovich

\*******************************************************************/

#ifndef __CPROVER_LOOPFROG_INVARIANTS_TI_LESS_GREATER_ALL_H_
#define __CPROVER_LOOPFROG_INVARIANTS_TI_LESS_GREATER_ALL_H_

#include "invariant_test.h"

class ti_less_greater_all_invariant_testt :
  public invariant_testt
{
public:
  ti_less_greater_all_invariant_testt(
    contextt &context) : 
      invariant_testt("TI2", "var' >/< var", context, TRANSITION),
      ns(context) {}
  
  virtual ~ti_less_greater_all_invariant_testt(void) {}
  
  virtual void get_transition_invariants(
    const loop_summaryt &summary,
    transition_invariantst &candidates);

protected:
  const namespacet ns;

};

#endif /*__CPROVER_LOOPFROG_INVARIANTS_TI_LESS_GREATER_ALL_H_*/
