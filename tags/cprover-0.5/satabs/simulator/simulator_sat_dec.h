/*******************************************************************\

Module: SAT-based Decision Procedure for Simulator

Author: Daniel Kroening
    
Date: October 2004

Purpose: Simulate an abstract counterexample on the concrete program
         to determmine whether it is spurious.

\*******************************************************************/

#ifndef CPROVER_CEGAR_SIMULATOR_SAT_H
#define CPROVER_CEGAR_SIMULATOR_SAT_H

#include <solvers/sat/satcheck.h>
#include <solvers/flattening/bv_pointers.h>

class satcheck_wrappert
{
public:
  satcheckt satcheck;
};

class simulator_sat_dect:
  public satcheck_wrappert,
  public bv_pointerst
{
public:
  virtual const std::string description()
  { return "Bit vector SAT"; }
  
  explicit simulator_sat_dect(const namespacet &_ns):
    bv_pointerst(_ns, satcheck) { }
};

#endif
