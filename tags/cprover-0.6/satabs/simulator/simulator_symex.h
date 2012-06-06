/*******************************************************************\

Module: Simulator

Author: Daniel Kroening
        Karen Yorav
    
Date: June 2003

Purpose: Simulate an abstract counterexample on the concrete program
to determmine whether it is spurious.

\*******************************************************************/

#ifndef CPROVER_SATABS_SIMULATOR_SYMEX_H
#define CPROVER_SATABS_SIMULATOR_SYMEX_H

#include <namespace.h>

#include <solvers/prop/prop_conv.h>
#include <goto-symex/goto_symex_state.h>
#include <goto-symex/symex_target_equation.h>

#include "simulator.h"
#include "path_slicer.h"

class simulator_symext:public simulatort
{
public:
  simulator_symext(
    const argst &args,
    bool _path_slicing,
    bool _shortest_prefix):
    simulatort(args),
    path_slicing(_path_slicing),
    shortest_prefix(_shortest_prefix)
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
    fail_infot &fail_info);
  
  bool path_slicing;
  bool shortest_prefix;

protected:
  virtual bool check_prefix(
    const predicatest &predicates,
    const abstract_modelt &abstract_model,
    abstract_counterexamplet &abstract_counterexample,
    concrete_counterexamplet &concrete_counterexample,
    fail_infot &fail_info);
    
  void convert(
    prop_convt &prop_conv,
    symex_target_equationt &equation,
    symex_target_equationt::SSA_stepst::const_iterator last);
    
  struct prefixt
  {
    void clear()
    {
      equation.clear();
      step_map.clear();
    }
  
    prefixt(const namespacet &_ns):equation(_ns)
    {
    }
  
    symex_target_equationt equation;
    
    // map from SSA_steps to abstract steps
    typedef std::map<
      symex_target_equationt::SSA_stepst::const_iterator,
      abstract_counterexamplet::stepst::const_iterator> step_mapt;

    step_mapt step_map;

    // map from abstract steps to SSA_steps
    typedef std::map<
      abstract_counterexamplet::stepst::const_iterator,
      symex_target_equationt::SSA_stepst::const_iterator> SSA_step_mapt;

    SSA_step_mapt SSA_step_map;
    
    void record(
      symex_target_equationt::SSA_stepst::const_iterator SSA_step_it,
      abstract_counterexamplet::stepst::const_iterator step_it)
    {
      step_map[SSA_step_it]=step_it;
      SSA_step_map[step_it]=SSA_step_it;
    }

    abstract_counterexamplet::stepst::const_iterator get_abstract_step(
      symex_target_equationt::SSA_stepst::const_iterator e_it) const
    {
      step_mapt::const_iterator it=step_map.find(e_it);
      assert(it!=step_map.end());
      return it->second;
    }

    symex_target_equationt::SSA_stepst::const_iterator get_SSA_step(
      abstract_counterexamplet::stepst::const_iterator e_it) const
    {
      SSA_step_mapt::const_iterator it=SSA_step_map.find(e_it);
      assert(it!=SSA_step_map.end());
      return it->second;
    }

  };

  void build_equation_prefix(
    const abstract_counterexamplet &abstract_counterexample,
    prefixt &prefix,
    goto_symex_statet &state,
    bool constant_propagation);

  virtual bool check_prefix_equation(
    const abstract_counterexamplet &abstract_counterexample,
    prefixt &prefix,
    goto_symex_statet &state,
    concrete_counterexamplet &concrete_counterexample,
    fail_infot &fail_info);

  virtual bool check_full_trace(
    const abstract_counterexamplet &abstract_counterexample,
    prefixt &prefix,
    goto_symex_statet &state,
    concrete_counterexamplet &concrete_counterexample,
    fail_infot &fail_info);

  bool is_satisfiable(decision_proceduret &decision_procedure)
  {
    decision_procedure.set_message_handler(get_message_handler());
    decision_procedure.set_verbosity(get_verbosity());
  
    // solve it
    switch(decision_procedure.dec_solve())
    {
    case decision_proceduret::D_UNSATISFIABLE:
      return false;

    case decision_proceduret::D_SATISFIABLE:
      return true;

    default:
      throw "unexpected result from dec_solve()";
    }
  }

  void get_fail_info(
    const abstract_counterexamplet &abstract_counterexample,
    const class simulator_sat_dect &satcheck,
    const prefixt &prefix,
    const symex_target_equationt::SSA_stepst::const_iterator c_it,
    fail_infot &fail_info);
};

#endif
