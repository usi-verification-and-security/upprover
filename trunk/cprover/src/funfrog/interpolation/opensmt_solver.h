/*******************************************************************\

Module: An OpenSMT backend as an interpolating solver.

Author: Ondrej Sery

\*******************************************************************/

#ifndef CPROVER_OPENSMT_SOLVER_H
#define CPROVER_OPENSMT_SOLVER_H

#include "interpolating_solver.h"

// A wrapper for the OpenSMT interpolating solver
class opensmt_solvert : public interpolating_solvert
{
public:
  explicit opensmt_solvert(const namespacet &_ns):interpolating_solvert(_ns)
  {
  }

  // Begins a partition of formula for latter reference during 
  // interpolation extraction. All assertions made until
  // next call of new_partition() will be part of this partition.
  //
  // returns a unique partition id
  virtual fle_part_idt new_partition();

  // Extracts the symmetric interpolant of the specified set of
  // partitions. This method can be called only after previous
  // call to dec_solve(), returning the decision_proceduret::D_UNSATISFIABLE
  // result
  virtual exprt get_interpolant(const fle_part_idst& partition_ids) const;
};

#endif
