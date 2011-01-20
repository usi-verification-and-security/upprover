/*******************************************************************\

Module: Interface for a decision procedure with (symmetric) 
interpolation.

Author: Ondrej Sery

\*******************************************************************/

#ifndef INTERPOLATING_SOLVER_H_
#define INTERPOLATING_SOLVER_H_

#include <decision_procedure.h>

class interpolating_solvert:public decision_proceduret
{
public:
  explicit interpolating_solvert(const namespacet &_ns) : 
        decision_proceduret(_ns)
  {
  }

  // Begins a partition of formula for latter reference during 
  // interpolation extraction. The partitions can be nested.
  // All assertions made until the corresponding call of
  // pop_partition() will be part of this partition.
  //
  // returns a unique partition id
  virtual int push_partition()=0;

  // Ends a partition of formula for latter interpolation
  virtual void pop_partition()=0;

  // Extracts the symmetric interpolant of the specified 
  // partition. This method can be called only after previous
  // call to dec_solve(), returning the result
  // decision_proceduret::D_UNSATISFIABLE
  virtual exprt get_interpolant(int partition_id) const=0;
};

#endif

