/*******************************************************************\

Module: Simulator using Interpolants

Author: Daniel Kroening
    
Date: September 2005

Purpose: Simulate an abstract counterexample on the concrete program
         to determmine whether it is spurious.

\*******************************************************************/

#ifndef CPROVER_SATABS_SIMULATOR_IPP_H
#define CPROVER_SATABS_SIMULATOR_IPP_H

#include "simulator_symex.h"

class simulator_ippt:public simulator_symext
{
private:
  int limit;

public:
  simulator_ippt(const argst &args, int _limit):
    simulator_symext(args, false, true),
    limit(_limit)
  {
  }

  bool check_prefix(
    const predicatest &predicates,
    const abstract_modelt &abstract_model,
    abstract_counterexamplet &abstract_counterexample,
    concrete_counterexamplet &concrete_counterexample,
    fail_infot &fail_info);

  expr_listt interpolant_list;  

protected:
  virtual bool check_prefix_equation(
    prefixt &prefix,
    goto_symex_statet &state,
    concrete_counterexamplet &concrete_counterexample,
    fail_infot &fail_info);
};

#endif
