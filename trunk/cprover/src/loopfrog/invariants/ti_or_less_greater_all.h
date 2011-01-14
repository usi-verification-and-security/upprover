/*******************************************************************

 Module: disjunction of all strict order pairs >/< for all varibles
 		 while the other variables are untouched
         (a'>a and b'=b) or...
 Author: Aliaksei Tsitovich

\*******************************************************************/

#ifndef __CPROVER_LOOPFROG_INVARIANTS_TI_OR_LESS_GREATER_ALL_H_
#define __CPROVER_LOOPFROG_INVARIANTS_TI_OR_LESS_GREATER_ALL_H_

#include "invariant_test.h"

class ti_or_less_greater_all_invariant_testt :
  public invariant_testt
{
public:
  ti_or_less_greater_all_invariant_testt(
    contextt &context) : 
      invariant_testt("TI5", "(a'>a and b'=b) or...", context, TRANSITION),
      ns(context) {}
  
  virtual ~ti_or_less_greater_all_invariant_testt(void) {}
  
  virtual void get_transition_invariants(
    const loop_summaryt &summary,
    transition_invariantst &candidates);

protected:
  const namespacet ns;

};

#endif /*__CPROVER_LOOPFROG_INVARIANTS_TI_OR_LESS_GREATER_ALL_H_*/
