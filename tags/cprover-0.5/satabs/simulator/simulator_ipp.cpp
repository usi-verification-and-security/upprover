/*******************************************************************\

Module: Simulator for Prefixes using Interpolants

Author: Daniel Kroening

Date: August 2005

Purpose: 

\*******************************************************************/

#include <base_type.h>

#include <goto-symex/goto_symex_state.h>
#include <ipp/interpolating_tp.h>

#include "simulator_ipp.h"

/*******************************************************************\

Function: simulator_ippt::check_prefix_equation

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
  
bool simulator_ippt::check_prefix_equation(
  prefixt &prefix,
  goto_symex_statet &state,
  concrete_counterexamplet &concrete_counterexample,
  fail_infot &fail_info)
{
  interpolating_tpt interpolating_tp(limit);

  for(symex_target_equationt::statest::const_iterator
      c_it=prefix.equation.states.begin();
      c_it!=prefix.equation.states.end();
      c_it++)
  {
    exprt tmp(c_it->cond);

    if(tmp.is_nil()) tmp.make_true();

    ::base_type(tmp, ns);
                        
    if(c_it->is_assert())
      interpolating_tp.set_to_false(tmp);
    else
      interpolating_tp.set_to_true(tmp);
  }

  switch(interpolating_tp.dec_solve())
  {
  case decision_proceduret::D_TAUTOLOGY:
  case decision_proceduret::D_SATISFIABLE:
    return false;
  
  case decision_proceduret::D_UNSATISFIABLE:
    status("Counterexample prefix is spurious");

    interpolating_tp.get_interpolant_list().swap(interpolant_list);
    
    Forall_expr_list(it, interpolant_list)
      state.get_original_name(*it);

    return true;
  
  default:
    throw "error from interpolating theorem prover";
  }
}

/*******************************************************************\

Function: simulator_ippt::check_prefix

  Inputs:

 Outputs:

 Purpose: check an abstract counterexample
          Returns TRUE if the counterexample is spurious,
          and FALSE otherwise

\*******************************************************************/

bool simulator_ippt::check_prefix(
  const predicatest &predicates,
  const abstract_modelt &abstract_model,
  abstract_counterexamplet &abstract_counterexample,
  concrete_counterexamplet &concrete_counterexample,
  fail_infot &fail_info)
{
  assert(abstract_counterexample.steps.size()!=0);

  // clean up
  concrete_counterexample.clear();

  // build equation
  prefixt prefix(ns);
  goto_symex_statet state;

  build_equation_prefix(abstract_counterexample, prefix, state, false);

  #if 0
  std::cout << prefix.equation;
  #endif
  
  // run decision procedure
  
  return check_prefix_equation(
    prefix,
    state,
    concrete_counterexample,
    fail_info);
}
