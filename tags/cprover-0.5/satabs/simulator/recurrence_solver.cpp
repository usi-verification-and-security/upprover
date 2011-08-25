/*******************************************************************\

Module: Simulator/Solving Recurrences

Author: Georg Weissenbacher

Date: June 2006

Purpose: 

\*******************************************************************/

#define DEBUG

#include <algorithm>
#include <iterator>

#include <replace_expr.h>
#include <simplify_expr.h>
#include <i2string.h>
#include <arith_tools.h>

#include <goto-symex/goto_symex.h>

#include "recurrence_solver.h"

/*******************************************************************\

Function: recurrence_solver::referenced_subexpressions

  Inputs:

 Outputs:

 Purpose: Finds all references to an element in expressions in expr

\*******************************************************************/

void recurrence_solver::referenced_subexpressions(
  const exprt expr,
  const std::set<exprt> &expressions,
  std::set<exprt> &result)
{
  // continue recursively
  forall_operands (it, expr)
    {
      referenced_subexpressions(*it, expressions, result);
    }

  // now check if the current expression is referenced
  if (expressions.find (expr) != expressions.end ())
    {
      result.insert (expr);
    }
}

/*******************************************************************\

Function: recurrence_solver::referenced_parameters

  Inputs:

 Outputs:

 Purpose: Finds references to loop induction parameters

\*******************************************************************/

void recurrence_solver::referenced_parameters(
  const goto_symex_statet &state,
  const exprt expr,
  minimization_listt &result)
{
  if (expr.get_bool("induction_symbol"))
    {
      exprt tmp = expr;
      state.get_original_name(tmp);
      // check if this is a SSA variable, if not, insert
      if (tmp == expr)
        result.insert (expr);
      return;
    }

  // continue recursively
  forall_operands (it, expr)
    {
      referenced_parameters(state, *it, result);
    }
}

/*******************************************************************\

Function: recurrence_solver::reorder_problem

  Inputs:

 Outputs:

 Purpose: Reorders the recurrence problem according to dependencies

\*******************************************************************/

void recurrence_solver::reorder_problem(
  const std::map<exprt, exprt> &problem,
  std::list<exprt> &sorted)
{
  // Get the set of all rhs
  std::set<exprt> targets;
  // The dependency map
  std::map<exprt, std::set<exprt> > dependencies;

  // Create set of all assigned variables
  for(std::map<exprt, exprt>::const_iterator
        p_it=problem.begin();
      p_it!=problem.end();
      p_it++)
    {
      targets.insert (p_it->first);
    }
  
  for(std::map<exprt, exprt>::const_iterator
        p_it=problem.begin();
      p_it!=problem.end();
      p_it++)
    {
      std::set<exprt> references;
      // find all references in rhs to an element in targets
      referenced_subexpressions (p_it->second, targets, references);
      // remove self references (e.g., N$1 = N$1)
      references.erase (p_it->first);
      dependencies[p_it->first] = references;
    }
  
  // Sort the problems according to their dependencies
  // The variables the problems refer to define a partial order
  // so use topological sorting
  
  while (dependencies.size () > 0)
    {
      // find an element that does not reference any LHSs
      for(std::map<exprt, std::set<exprt> >::const_iterator
            d_it=dependencies.begin();
          d_it!=dependencies.end();
          d_it++)
        {
          std::set<exprt> result;
          std::insert_iterator<std::set<exprt> >  
            r_it (result, result.begin());

          std::set_intersection ((d_it->second).begin (),
                                 (d_it->second).end (),
                                 targets.begin (), 
                                 targets.end (),
                                 r_it);

          if (result.size () == 0)
            {
              sorted.push_back (d_it->first);
              
              // make sure we don't encounter this again
              std::set<exprt>::const_iterator t_it =
                targets.find (d_it->first);
              assert (t_it != targets.end ());
              targets.erase (t_it);
              dependencies.erase (d_it->first);
              break;
            }
        }
    }
}

/*******************************************************************\

Function: recurrence_solver::substitute_problem

  Inputs:

 Outputs:

 Purpose: Subsitute the problems such that repeated occurrences
          of a variable are not considered separate problems. This
          is conservative, because we hope to find better solutions
          if we keep the recurrences simple. (A more aggressive
          approach would be to substitute all LHS occurrences in all
          RHS expressions of the problem)

\*******************************************************************/

void recurrence_solver::substitute_problem(
  std::map<exprt, exprt> &problem,
  const std::list<exprt> &sorted,
  const goto_symex_statet &initial_state,
  const goto_symex_statet &final_state)
{
  for (std::list<exprt>::const_iterator l_it = sorted.begin ();
       l_it != sorted.end (); ) // l_it is increased in inner loop
    {
      const exprt &subst_lhs = *l_it;
      irep_idt lhs_name = 
        final_state.get_original_name (subst_lhs.get ("identifier"));
      
      // this can only be referenced in later problem instances
      for (std::list<exprt>::const_iterator m_it = ++l_it;
           m_it != sorted.end (); m_it++)
        {
          const exprt &curr_lhs = *m_it;
          irep_idt name = 
            final_state.get_original_name (curr_lhs.get ("identifier"));
          if (lhs_name == name)
            {
              // perform substitution!
              const exprt &subst_expr = problem[subst_lhs]; 
              exprt rhs_expr = problem[curr_lhs];

              replace_expr (subst_lhs, subst_expr, rhs_expr);

              problem[curr_lhs] = rhs_expr;
            }
        }
    }
}

/*******************************************************************\

Function: recurrence_solver::is_recurrence

  Inputs: a recurrence equation and the initial and final
          states of the loop

 Outputs: false if the lhs variable doesn't occur on the rhs

 Purpose: Used to check if an assignment is a recurrence
    

\*******************************************************************/

bool recurrence_solver::is_recurrence(
  const exprt &lhs,
  const exprt &recurrence,
  const goto_symex_statet &initial_state,
  const goto_symex_statet &final_state,
  const std::set<exprt> &start_values,
  const std::set<exprt> &end_values)
{
  irep_idt lhs_name = 
    final_state.get_original_name (lhs.get ("identifier"));

  if (end_values.find (lhs) == end_values.end ())
    return false;
  
  std::set<exprt> references;
  // find all references in recurrence to initial elements
  referenced_subexpressions (recurrence, start_values, references);

  // check if initial value of lhs is mentioned on rhs
  for (std::set<exprt>::const_iterator it = references.begin ();
       it != references.end (); it++)
    {
      const exprt &var = *it;
      irep_idt orig_name = 
        initial_state.get_original_name (var.get ("identifier"));
      
      if (lhs_name == orig_name)
        {
          return true;
        }
    }

  return false;
}


/*******************************************************************\

Function: recurrence_solver::match_recurrence

  Inputs: a recurrence equation, a paramter and references
          to empty expression objects for alpha, beta and gamma

 Outputs: false if recurrence does not match, true and modified
          values for alpha, beta and gamma if it does

 Purpose: Tries to match a recurrent equation:
          i_0 = alpha, i_n = i_{n-1} + \beta + \gamma\cdot n, 
          where n > 0 refers to the parameter. The result will
          be used to construct following solution:
          i_n = alpha + beta * n + gamma * (n * (n+1))/ 2
    

\*******************************************************************/

bool recurrence_solver::match_recurrence(
  const exprt &lhs,
  const exprt &recurrence,
  const exprt &parameter,
  const goto_symex_statet &initial_state,
  const goto_symex_statet &final_state,
  const std::set<exprt> &start_values,
  const std::set<exprt> &end_values,
  exprt& alpha, 
  exprt& beta, 
  exprt& gamma)
{
  std::set<exprt> constants;
  exprt uncasted_recurrence;

  irep_idt lhs_name = 
    final_state.get_original_name (lhs.get ("identifier"));

  alpha.make_nil ();
  beta.make_nil ();
  gamma.make_nil ();

  if (end_values.find (lhs) == end_values.end ())
    return false;

  // unpack recurrence if necessary
  if (recurrence.id() == "typecast")
    uncasted_recurrence = recurrence.op0();
  else
    uncasted_recurrence = recurrence;

  // try matching addition
  if(uncasted_recurrence.id()=="+" &&
     uncasted_recurrence.operands().size()>=2)
    {
      forall_operands (it, uncasted_recurrence)
        {
          const exprt &op = *it;
          exprt uncasted_op;

          if (op.id() == "typecast")
            uncasted_op = op.op0();
          else
            uncasted_op = op;

          if (uncasted_op.is_constant ())
            {
              constants.insert (op);
            }
          else if (start_values.find(uncasted_op)!=start_values.end())
            {
              // check if this is the previous value of lhs
              irep_idt name = 
                initial_state.get_original_name (uncasted_op.get ("identifier"));
              if (name == lhs_name)
                {
                  // this is what we were searching for
                  alpha = op;
                }
              else
                {
                  // otherwise handle it as a constant
                  constants.insert (op);
                }
            }
          else if (uncasted_op == parameter)
            {
              gamma = from_integer (1, parameter.type()); 
            }
          else if (uncasted_op.id()=="*")
            {
              if (uncasted_op.op0().is_constant () &&
                  (uncasted_op.op1() == parameter || 
                   (uncasted_op.op1().id() == "typecast" && 
                    uncasted_op.op1().op0() == parameter))
                  ) // assumption: constant always first
                {
                  if (gamma.is_nil ())
                    gamma = uncasted_op.op0 ();
                  else
                    return false;
                }
            }
        }
    }
  
  if (alpha.is_nil () ||
      constants.size() + (gamma.is_nil ()? 0:1) != 
      uncasted_recurrence.operands().size() - 1)
    return false;
  
  // construct the sum for beta
  if (constants.size () > 1)
    {
      beta = exprt ("+", (*constants.begin()).type ());
      
      for (std::set<exprt>::const_iterator it = constants.begin ();
           it != constants.end (); it++)
        {
          exprt casted_constant = *it;
          if (casted_constant.type () != beta.type ())
            casted_constant.make_typecast (beta.type ());
          beta.move_to_operands (casted_constant);
        }
    }
  else if (constants.size () == 1)
    beta = *(constants.begin ());
  
  return true;
}


/*******************************************************************\

Function: recurrence_solver::construct_recurrence

Inputs:  the parameters alpha, beta and gamma of the recurrence
         and the parameter n

Outputs: alpha + beta * n + gamma * (n * (n+1))/ 2. Result is
         stored in solution_expr. The objects alpha, beta and
         gamma might be destroyed!

Purpose: construct the recurrence corresponding to the result
         of match_recurrence
    

\*******************************************************************/

void recurrence_solver::construct_recurrence(
  const exprt &lhs,
  const exprt &parameter,
  exprt& alpha, 
  exprt& beta, 
  exprt& gamma,
  exprt &solution_expr)
{
  
  // construct lhs = alpha + beta * n + gamma * (n * (n+1))/ 2
  solution_expr = exprt ("+", lhs.type ());
  
  solution_expr.move_to_operands (alpha);
  
  if (!beta.is_nil ())
    {
      exprt casted_parameter=parameter;
      if(casted_parameter.type()!=beta.type())
        casted_parameter.make_typecast(beta.type());

      if (beta.is_one ())
        {
          solution_expr.copy_to_operands (casted_parameter);
        }
      else
        {
          // put in multiplication, if necessary
          exprt mult=exprt("*", beta.type());
          mult.copy_to_operands(beta, casted_parameter);
          solution_expr.copy_to_operands (mult);
        }
    }
  
  if (!gamma.is_nil ())
    {
      exprt casted_parameter=parameter;
      if(casted_parameter.type()!=gamma.type())
        casted_parameter.make_typecast(gamma.type());

      // construct (n+1)
      exprt plus=exprt("+", gamma.type());
      exprt one=from_integer (1, gamma.type ());
      plus.copy_to_operands(casted_parameter, one);
      // construct n*(n+1)
      exprt mult=exprt("*", gamma.type());
      mult.copy_to_operands(casted_parameter);
      mult.move_to_operands(plus);
      // construct n*(n+1)/2
      exprt div=exprt("/", gamma.type());
      exprt two=from_integer (2, gamma.type ());
      div.move_to_operands(mult,two);
      
      if (gamma.is_one())
        {
          // cast?
          exprt casted_div = div;
          if (casted_div.type()!=solution_expr.type())
            casted_div.make_typecast(solution_expr.type());
          
          solution_expr.move_to_operands (casted_div);
        }
      else
        {
          exprt gamma_mul=exprt("*", gamma.type());
          gamma_mul.move_to_operands (gamma, div);
          // cast?
          exprt casted_gamma_mul = gamma_mul;
          if(casted_gamma_mul.type()!=solution_expr.type())
            casted_gamma_mul.make_typecast(solution_expr.type());
          // add to solution_expr
          solution_expr.move_to_operands (casted_gamma_mul);
        }
    }
}


/*******************************************************************\

Function: recurrence_solver::solve_recurrence

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void recurrence_solver::solve_recurrence(
  const exprt &parameter,
  const std::set<exprt> &start_values,
  const std::set<exprt> &end_values,
  const goto_symex_statet &initial_state,
  const goto_symex_statet &final_state,
  const std::map<exprt, exprt> &problem,
  replace_mapt &solution,
  const namespacet &ns)
{
  unsigned nondet_count=0;

  std::list<exprt> sorted;
  reorder_problem (problem, sorted);
  assert (problem.size() == sorted.size());

  std::map<exprt, exprt> modified_problem = problem;
  substitute_problem (modified_problem, sorted, initial_state, final_state);

  for (std::list<exprt>::const_iterator l_it = sorted.begin ();
       l_it != sorted.end (); ) // l_it is increased at end of loop
  {
    std::map<exprt, exprt>::const_iterator p_it =  
      modified_problem.find (*l_it);
    assert (p_it != modified_problem.end ());
    
    const exprt &lhs = p_it->first;
    
    // try to get rhs in some specific shape
    exprt tmp_rhs(p_it->second);
    simplify(tmp_rhs, ns);
    
    exprt solution_expr;
    solution_expr.make_nil();
    
#if 0
    std::cout << "TMP_RHS: " << tmp_rhs.pretty() << std::endl;
#endif
    
    exprt alpha, beta, gamma;
    
    if (match_recurrence (lhs,
                          tmp_rhs,
                          parameter,
                          initial_state,
                          final_state,
                          start_values,
                          end_values,
                          alpha,
                          beta,
                          gamma))
      {
        construct_recurrence (lhs, 
                              parameter, 
                              alpha, beta, gamma, 
                              solution_expr);
      }
    else if (is_recurrence (lhs, 
                            tmp_rhs, 
                            initial_state, 
                            final_state, 
                            start_values,
                            end_values))
      {
        // could not solve, so make it non-deterministic
        exprt nondet("nondet_symbol", lhs.type());
        nondet.set("identifier", "recurrence$"+i2string(++nondet_count));
        solution_expr=nondet;
      }
    else
      {
        // no changes
        solution_expr=tmp_rhs;  
      }
    
    solution[lhs]=solution_expr;
    
    // now subsitute the result in the remaining problem instances
    for (std::list<exprt>::const_iterator tail_it = ++l_it;
         tail_it != sorted.end (); ++tail_it)
      {
        const exprt &lhs_expr = *tail_it;
        exprt rhs_expr = modified_problem[lhs_expr];
        
        replace_expr (lhs, solution_expr, rhs_expr);

        modified_problem[lhs_expr] = rhs_expr;
      }
  }
}

/*******************************************************************\

Function: recurrence_solver::cleanup_recurrence_predicates

  Inputs:

 Outputs:

 Purpose: Makes sure that the right hand side of the refinement
          predicates generated by the recurrence solver does not
          mix up variables that are changed in the loop body
          and the initial values of the variables

\*******************************************************************/

void recurrence_solver::cleanup_recurrence_predicates(
  symex_target_equationt &equation,
  unsigned state_number,
  goto_symex_statet &final_state,
  const std::map<exprt, exprt> &problem,
  std::map<goto_programt::const_targett,exprt> &closed_forms,
  std::list<exprt> &predicates,
  const namespacet &ns)
{
  // construct the set of modified variables
  std::set<exprt> modified;

  std::map<exprt, exprt>::const_iterator prob_it;
  for (prob_it = problem.begin ();
       prob_it != problem.end ();
       prob_it++)
    {
      exprt lhs = prob_it->first;
      final_state.get_original_name (lhs);
      modified.insert (lhs);
    }

  // now perform substitutions on the predicate until the (renamed)
  // left hand sides doesn't refer to modified variables anymore
  symex_target_equationt::SSA_stepst::iterator
    start_it=equation.get_SSA_step(state_number);

  for (std::map<goto_programt::const_targett,exprt>::iterator c_it = 
         closed_forms.begin ();
       c_it != closed_forms.end ();
       c_it++)
    {
      exprt &predicate = c_it->second;

      symex_target_equationt::SSA_stepst::reverse_iterator s_it;
      for (s_it = symex_target_equationt::SSA_stepst::reverse_iterator(start_it);
           s_it != equation.SSA_steps.rend();
           s_it++)
        {
          symex_target_equationt::SSA_stept &s=*s_it;
          
          if (modified.find (s.original_lhs) != modified.end())
            {
              replace_expr (s.lhs, s.rhs, predicate);
            }
        }
  
      simplify(predicate, ns);
      final_state.get_original_name(predicate);
      // add this to the set of refinement predicates
      predicates.push_back(predicate);
    }
}
