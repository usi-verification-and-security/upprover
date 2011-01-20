/*******************************************************************\

Module: An OpenSMT backend as an interpolating solver.

Author: Ondrej Sery

\*******************************************************************/

#ifndef OPENSMT_SOLVER_H_
#define OPENSMT_SOLVER_H_

#include "interpolating_solver.h"

// A wrapper for the OpenSMT interpolating solver
class opensmt_solvert : public interpolating_solvert
{
public:
  explicit opensmt_solvert(const namespacet &_ns):interpolating_solvert(_ns)
  {
  }

  // Begins a partition of formula for latter reference during 
  // interpolation extraction. The partitions can be nested.
  // All assertions made until the corresponding call of
  // pop_partition() will be part of this partition.
  //
  // returns a unique partition id
  virtual int push_partition();

  // Ends a partition of formula for latter interpolation
  virtual void pop_partition();

  // Extracts the symmetric interpolant of the specified 
  // partition. This method can be called only after previous
  // call to dec_solve(), returning the result
  // decision_proceduret::D_UNSATISFIABLE
  virtual exprt get_interpolant(int partition_id) const;
};

#endif

