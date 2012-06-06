/*******************************************************************\

Module: Simulator

Author: Daniel Kroening
        Karen Yorav
    
Date: June 2003

Purpose: Simulate an abstract counterexample on the concrete program
to determmine whether it is spurious.

\*******************************************************************/

#ifndef CPROVER_CEGAR_SIMULATOR_H
#define CPROVER_CEGAR_SIMULATOR_H

#include "../loop_component.h"
#include "../modelchecker/abstract_counterexample.h"
#include "../simulator/concrete_counterexample.h"
#include "../abstractor/predicates.h"
#include "fail_info.h"

class simulatort:public loop_componentt
{
public:
  simulatort(const argst &args):
    loop_componentt(args)
  {
  }

  // Returns TRUE if the counterexample is spurious,
  // and FALSE otherwise. If FALSE is returned, a concrete
  // counterexample is provided as well
  
  virtual bool is_spurious(
    const predicatest &predicates,
    const abstract_modelt &abstract_model,
    abstract_counterexamplet &abstract_counterexample,
    concrete_counterexamplet &concrete_counterexample,
    fail_infot &fail_info)=0;
};

#endif
