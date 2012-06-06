/*******************************************************************

 Module: An iterator bounds invariant

 Author: CM Wintersteiger

\*******************************************************************/

#ifndef __CPROVER_LOOPFROG_INVARIANTS_ITERATOR_BOUNDS_H_
#define __CPROVER_LOOPFROG_INVARIANTS_ITERATOR_BOUNDS_H_

#include "invariant_test.h"

class iterator_bounds_invariant_testt : 
  public invariant_testt
{
public:
  iterator_bounds_invariant_testt(
    contextt &context) : 
      invariant_testt("IB", "Iterator Bounds", context),
      ns(context) {}
  
  virtual ~iterator_bounds_invariant_testt(void) {}
  
  virtual void get_invariants(
    const loop_summaryt &summary,
    std::set<exprt> &potential_invariants);

protected:
  const namespacet ns;
  
  void find_indexes(
    const std::set<exprt> &from,
    std::set<exprt> &to) const;
  
  void find_indexes(
    const exprt &expr,
    std::set<exprt> &to) const;
};

#endif /*__CPROVER_LOOPFROG_INVARIANTS_ITERATOR_BOUNDS_H_*/
