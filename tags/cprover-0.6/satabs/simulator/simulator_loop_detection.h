/*******************************************************************\

Module: Simulator

Author: Daniel Kroening
    
Date: January 2006

Purpose: Simulate an abstract counterexample on the concrete program
         to determmine whether it is spurious.

\*******************************************************************/

#ifndef CPROVER_SATABS_SIMULATOR_SYMEX_LOOP_DETECTION_H
#define CPROVER_SATABS_SIMULATOR_SYMEX_LOOP_DETECTION_H

#include <stack>

#include <mp_arith.h>

#include <goto-symex/goto_symex_state.h>

#include "simulator_sat_dec.h"

#include "simulator_symex.h"

class simulator_loop_detectiont:public simulator_symext
{
public:
  simulator_loop_detectiont(
    const argst &args,
    contextt &_shadow_context,
    bool _path_slicing,
    bool _shortest_prefix):
    simulator_symext(args, _path_slicing, _shortest_prefix),
    parameter_index(0),
    shadow_context(_shadow_context)
  {
  }

protected:
  virtual bool check_prefix(
    const predicatest &predicates,
    const abstract_modelt &abstract_model,
    abstract_counterexamplet &abstract_counterexample,
    concrete_counterexamplet &concrete_counterexample,
    fail_infot &fail_info);
  
  // Phase I

  struct loop_begint
  {
    unsigned state_nr;
    goto_symex_statet state;
    mp_integer unwindings;
    abstract_counterexamplet::stepst::const_iterator c_it;
    
    loop_begint():unwindings(0)
    {
    }
  };

  typedef std::stack<loop_begint> loop_stackt;
  typedef std::pair<
    abstract_counterexamplet::stepst::const_iterator,
    mp_integer> loop_headt;
  typedef std::list<loop_headt> loop_headst;

  void build_parameterized_equation(
    const abstract_counterexamplet &abstract_counterexample,
    symex_target_equationt &equation,
    goto_symex_statet &state,
    fail_infot &fail_info,
    prefixt::step_mapt &step_map);
    
  exprt rename(goto_symex_statet &state, const exprt &expr) const
  {
    exprt tmp(expr);
    state.rename(tmp, concrete_model.ns);
    return tmp;
  }

  void build_loop_recurrence(
    symex_target_equationt &equation,
    goto_symex_statet &state,
    loop_begint &loop_begin,
    const exprt &parameter_expr,
    std::list<exprt> &recurrences,
    std::map<goto_programt::const_targett,code_assignt> &instructions,
    std::map<goto_programt::const_targett,exprt> &closed_forms);

  void get_fresh_induction_parameter(
    exprt &parameter);

  static void check_for_induction_variables(
    const abstract_counterexamplet::stepst prefix,
    const abstract_counterexamplet::stepst body,
    std::set<exprt>& variables);

  void fill_loop_info(
    const abstract_counterexamplet &abstract_counterexample,
    const abstract_counterexamplet::stepst::const_iterator start_it,
    const abstract_counterexamplet::stepst::const_iterator end_it,
    fail_infot::induction_infot &induction_info);
  
  struct loop_infot
  {
    exprt parameter;
    mp_integer parameter_value;
  };
  
  typedef std::list<loop_infot> loop_infost;
  loop_infost loop_infos;

  unsigned parameter_index;

  contextt& shadow_context;

  bool check_phase_I_equation(
    symex_target_equationt &equation,
    goto_symex_statet &state,
    const abstract_counterexamplet &abstract_counterexample,
    concrete_counterexamplet &phase_I_counterexample,
    prefixt::step_mapt &step_map,
    fail_infot &fail_info
);

  void minimize_parameters(
    simulator_sat_dect &satcheck,
    const symex_target_equationt &equation);

  
  // Phase II

  void unwind_counterexample(
    const abstract_counterexamplet &abstract_counterexample,
    const concrete_counterexamplet &phase_I_counterexample,
    abstract_counterexamplet &unwound_counterexample);
};

#endif
