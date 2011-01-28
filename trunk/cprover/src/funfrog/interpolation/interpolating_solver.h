/*******************************************************************\

Module: Interface for a decision procedure with (symmetric) 
interpolation.

Author: Ondrej Sery

\*******************************************************************/

#ifndef CPROVER_INTERPOLATING_SOLVER_H
#define CPROVER_INTERPOLATING_SOLVER_H

#include <set>

#include <decision_procedure.h>

typedef int fle_part_idt;
typedef std::vector<fle_part_idt> fle_part_idst;

class interpolating_solvert:public decision_proceduret
{
public:
  explicit interpolating_solvert(const namespacet &_ns) : 
        decision_proceduret(_ns)
  {
  }

  // Begins a partition of formula for latter reference during 
  // interpolation extraction. All assertions made until
  // next call of new_partition() will be part of this partition.
  //
  // returns a unique partition id
  virtual fle_part_idt new_partition()=0;

  // Extracts the symmetric interpolant of the specified set of
  // partitions. This method can be called only after previous
  // call to dec_solve(), returning the decision_proceduret::D_UNSATISFIABLE
  // result
  virtual exprt get_interpolant(const fle_part_idst& partition_ids) const=0;
};

#endif
