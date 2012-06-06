/*******************************************************************

 Module: A combination of state and transition invariants
         a>=0  => a' >/< a
 Author: Aliaksei Tsitovich

\*******************************************************************/
#ifndef __CPROVER_LOOPFROG_INVARIANTS_STI_GZERO_IMPLIES_LESS_GREATER_ALL_H_
#define __CPROVER_LOOPFROG_INVARIANTS_STI_GZERO_IMPLIES_LESS_GREATER_ALL_H_

#include "invariant_test.h"

class sti_gzero_implies_less_greater_all_invariant_testt :
  public invariant_testt
{
public:
  sti_gzero_implies_less_greater_all_invariant_testt(
    contextt &context) : 
      invariant_testt("ST1", "a>=0 => a' >/< a", context, STATE_AND_TRANSITION),
      ns(context) {}
  
  virtual ~sti_gzero_implies_less_greater_all_invariant_testt(void) {}
  
  virtual void get_transition_invariants(
    const loop_summaryt &summary,
    transition_invariantst &candidates);

protected:
  const namespacet ns;

  void find_indexes(
    const std::set<exprt> &from,
    std::set<exprt> &to) const;

  void find_indexes(
    const exprt &expr,
    std::set<exprt> &to) const;

};

#endif /*__CPROVER_LOOPFROG_INVARIANTS_STI_GZERO_IMPLIES_LESS_GREATER_ALL_H_*/
