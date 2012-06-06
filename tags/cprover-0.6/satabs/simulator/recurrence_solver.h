/*******************************************************************\

Module: Simulator/Solving Recurrences

Author: Georg Weissenbacher
    
Date: June 2006

Purpose: Solve recurrences 

\*******************************************************************/

#ifndef CPROVER_SATABS_SIMULATOR_RECURRENCE_SOLVER_H
#define CPROVER_SATABS_SIMULATOR_RECURRENCE_SOLVER_H

#include <expr.h>

#include <goto-symex/goto_symex_state.h>
#include <solvers/flattening/sat_minimizer.h>

#include "simulator_symex.h"

class recurrence_solver
{
protected:     
  static void referenced_subexpressions(
    const exprt expr,
    const std::set<exprt> &expressions,
    std::set<exprt> &result);

  static void reorder_problem(
    const std::map<exprt, exprt> &problem,
    std::list<exprt> &sorted);  

  static void substitute_problem(
    std::map<exprt, exprt> &problem,
    const std::list<exprt> &sorted,
    const goto_symex_statet &initial_state,
    const goto_symex_statet &final_state);  

  static bool is_recurrence(
    const exprt &lhs,
    const exprt &recurrence,
    const goto_symex_statet &initial_state,
    const goto_symex_statet &final_state,
    const std::set<exprt> &start_values,
    const std::set<exprt> &end_values);

  static bool match_recurrence(
    const exprt &lhs,
    const exprt &recurrence,
    const exprt &parameter,
    const goto_symex_statet &initial_state,
    const goto_symex_statet &final_state,
    const std::set<exprt> &start_values,
    const std::set<exprt> &end_values,
    exprt& alpha, 
    exprt& beta, 
    exprt& gamma);

  static void construct_recurrence(
    const exprt &lhs,
    const exprt &parameter,
    exprt& alpha, 
    exprt& beta, 
    exprt& gamma,
    exprt& solution_expr);

public:
  static void referenced_parameters(
    const goto_symex_statet &state,
    const exprt expr,
    minimization_listt &result);

  static void solve_recurrence(
    const exprt &parameter,
    const std::set<exprt> &start_values,
    const std::set<exprt> &end_values,
    const goto_symex_statet &initial_state,
    const goto_symex_statet &final_state,
    const std::map<exprt, exprt> &problem,
    replace_mapt &solution,
    const namespacet &ns);

  static void cleanup_recurrence_predicates(
    symex_target_equationt &equation,
    unsigned state_number,
    goto_symex_statet &final_state,
    const std::map<exprt, exprt> &problem,
    std::map<goto_programt::const_targett,exprt> &closed_forms,
    std::list<exprt> &predicates,
    const namespacet &ns);
};

#endif

