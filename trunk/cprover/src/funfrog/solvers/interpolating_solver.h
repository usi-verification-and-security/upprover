/*******************************************************************\

Module: Interface for a decision procedure with (symmetric) 
interpolation.

Author: Ondrej Sery

\*******************************************************************/

#ifndef CPROVER_INTERPOLATING_SOLVER_H
#define CPROVER_INTERPOLATING_SOLVER_H

#include <set>

#include <decision_procedure.h>

#include "prop_itp.h"

typedef int fle_part_idt;
typedef std::vector<fle_part_idt> fle_part_idst;
typedef std::vector<fle_part_idst> interpolation_taskt;

class interpolating_solvert
{
public:
  virtual ~interpolating_solvert() {};

  // Begins a partition of formula for latter reference during 
  // interpolation extraction. All assertions made until
  // next call of new_partition() will be part of this partition.
  //
  // returns a unique partition id
  virtual fle_part_idt new_partition()=0;

  // Extracts the symmetric interpolant of the specified set of
  // partitions. This method can be called only after solving the
  // the formula with an UNSAT result
  virtual void get_interpolant(const interpolation_taskt& partition_ids,
    interpolantst& interpolants) const=0;
};

#endif
