/*******************************************************************\

Module: Interface for a decision procedure with (symmetric) 
interpolation.

Author: Ondrej Sery

\*******************************************************************/

#ifndef CPROVER_interpolating_solver_H
#define CPROVER_interpolating_solver_H

#include <funfrog/solvers/itp_fwd.h>
#include "funfrog/solvers/interpolating_solver_fwd.h"

class symbol_exprt;

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

#ifdef PRODUCE_PROOF  
  // Extracts the symmetric interpolant of the specified set of
  // partitions. This method can be called only after solving the
  // the formula with an UNSAT result
  virtual void get_interpolant(const interpolation_taskt& partition_ids,
      interpolantst& interpolants) const = 0;

  // Is the solver ready for interpolation? I.e., the solver was used to decide
  // a problem and the result was UNSAT
  virtual bool can_interpolate() const=0;

  virtual void generalize_summary(itpt * interpolant, std::vector<symbol_exprt> & common_symbols) = 0;

#endif

  virtual void close_partition() = 0;

  virtual void insert_substituted(const itpt & itp, const std::vector<symbol_exprt> & symbols) = 0;
};

#endif
