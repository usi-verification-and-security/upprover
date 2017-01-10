/*******************************************************************\

Module: Interface for a decision procedure with (symmetric) 
interpolation.

Author: Ondrej Sery

\*******************************************************************/

#ifndef CPROVER_interpolating_solver_H
#define CPROVER_interpolating_solver_H

#include <set>
#include <decision_procedure.h>
#include "itp.h"
#include <opensmt/opensmt2.h>

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
      interpolantst& interpolants)=0;

  virtual void adjust_function(smt_itpt& itp, std::vector<symbol_exprt>& common_symbols, std::string fun_name, bool substitute = true)
  {assert(0);} // Only SMT should use it!

  // Is the solver ready for interpolation? I.e., the solver was used to decide
  // a problem and the result was UNSAT
  virtual bool can_interpolate() const=0;

};

#endif
