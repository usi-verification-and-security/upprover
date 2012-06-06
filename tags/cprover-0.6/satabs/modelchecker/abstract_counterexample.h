/*******************************************************************\

Module: Counterexamples

Author: Daniel Kroening
        Karen Yorav 

Date: June 2003

\*******************************************************************/

#ifndef CPROVER_CEGAR_ABSTRACT_COUNTEREXAMPLE_H
#define CPROVER_CEGAR_ABSTRACT_COUNTEREXAMPLE_H

#include "abstract_state.h"

/* An abstract conterexample */
class abstract_counterexamplet
{
public:
  typedef std::list<abstract_stept> stepst;
  stepst steps;
  
  bool has_loops() const;
    
  stepst::const_iterator get_step_nr(unsigned i) const;
  
  void swap(abstract_counterexamplet &other)
  {
    other.steps.swap(steps);
  }
  
  bool is_last_step(stepst::const_iterator it) const
  {
    return it==--steps.end();
  }
};

extern inline bool operator<(
  abstract_counterexamplet::stepst::const_iterator a,
  abstract_counterexamplet::stepst::const_iterator b)
{
  return (unsigned long int)&(*a)<(unsigned long int)&(*b);
}

std::ostream& operator<< (std::ostream& out,
                          const abstract_counterexamplet &counterexample);

#endif
