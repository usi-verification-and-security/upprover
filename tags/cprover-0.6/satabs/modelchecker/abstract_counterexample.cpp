/*******************************************************************\

Module: Counterexamples

Author: Daniel Kroening

  Date: June 2003

\*******************************************************************/

#include <assert.h>

#include "abstract_counterexample.h"

/*******************************************************************\

Function: abstract_counterexamplet::get_step_nr

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

abstract_counterexamplet::stepst::const_iterator
abstract_counterexamplet::get_step_nr(unsigned i) const
{
  stepst::const_iterator it=steps.begin();

  for(; i>0; i--)
  {
    assert(it!=steps.end());
    it++;
  }

  return it;
}

/*******************************************************************\

Function: abstract_counterexamplet::has_loops

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool abstract_counterexamplet::has_loops() const
{
  for(stepst::const_iterator
      it=steps.begin();
      it!=steps.end();
      it++)
    if(it->step_type==abstract_stept::LOOP_BEGIN)
      return true;
                                
  return false;
}
                                                                    
/*******************************************************************\

Function: operator <<

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::ostream &operator<<
 (std::ostream &out, const abstract_counterexamplet &counterexample)
{
  for(abstract_counterexamplet::stepst::const_iterator
      it=counterexample.steps.begin();
      it!=counterexample.steps.end();
      it++)
    out << *it;

  return out;
}
