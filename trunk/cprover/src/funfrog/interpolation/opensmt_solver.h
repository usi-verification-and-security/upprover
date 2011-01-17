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

  // Begins a partition of formula for latter interpolation
  virtual void push_partition(/* TODO: partition id */);

  // Ends a partition of formula for latter interpolation
  virtual void pop_partition();

  // Extracts the symmetric interpolant of the specified partition
  virtual exprt get_interpolant(/* TODO: partition id */) const;
};

#endif

