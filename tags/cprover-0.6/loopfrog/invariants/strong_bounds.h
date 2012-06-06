/*******************************************************************

 Module: An iterator bounds invariant

 Author: CM Wintersteiger

\*******************************************************************/

#ifndef __CPROVER_LOOPFROG_INVARIANTS_STRONG_BOUNDS_H_
#define __CPROVER_LOOPFROG_INVARIANTS_STRONG_BOUNDS_H_

#include "invariant_test.h"

class strong_bounds_invariant_testt : 
  public invariant_testt
{
public:
  strong_bounds_invariant_testt(
    contextt &context) : 
      invariant_testt("SB", "Strong It. Bounds", context),
      ns(context) {}
  
  virtual ~strong_bounds_invariant_testt(void) {}
  
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

#endif /*__CPROVER_LOOPFROG_INVARIANTS_STRONG_BOUNDS_H_*/
