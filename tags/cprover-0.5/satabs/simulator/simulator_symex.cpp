/*******************************************************************\

Module: Simulator

Author: Daniel Kroening

Date: October 2004

Purpose: Simulate an abstract counterexample on the concrete program
         to determmine whether it is spurious.

\*******************************************************************/

#include <assert.h>

#include <expr_util.h>
#include <i2string.h>

#include <solvers/sat/satcheck.h>
#include <solvers/flattening/bv_pointers.h>
#include <goto-symex/goto_symex.h>
#include <goto-symex/symex_target_equation.h>
#include <goto-symex/build_goto_trace.h>

#include "simulator_symex.h"
#include "simulator_sat_dec.h"

/*******************************************************************\

Function: simulator_symext::convert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void simulator_symext::convert(
  prop_convt &prop_conv,
  symex_target_equationt &equation,
  symex_target_equationt::SSA_stepst::const_iterator last)
{
  last++;
  
  for(symex_target_equationt::SSA_stepst::iterator
      it=equation.SSA_steps.begin();
      it!=last;
      it++)
  {
    it->guard_literal=const_literal(true);

    switch(it->type)
    {
    case goto_trace_stept::ASSIGNMENT:
    case goto_trace_stept::ASSUME:
      {
        exprt tmp=it->cond_expr;
        prop_conv.set_to_true(tmp);
        it->cond_literal=const_literal(true);
        #if 0
        std::cout << "CONSTRAINT: " << from_expr(ns, "", tmp) << std::endl;
        #endif
      }
      break;
    
    case goto_trace_stept::ASSERT:
      {
        exprt tmp=it->cond_expr;
        // we assume there is only one
        prop_conv.set_to_false(tmp);
        it->cond_literal=const_literal(false);
        #if 0
        std::cout << "CONSTRAINT: NOT " << from_expr(ns, "", tmp) << std::endl;
        #endif
      }
      break;

    case goto_trace_stept::LOCATION:
    case goto_trace_stept::OUTPUT:
    case goto_trace_stept::INPUT:
      break;
      
    default:
      assert(false);
    }
  }
}

/*******************************************************************\

Function: simulator_symext::build_equation_prefix

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void simulator_symext::build_equation_prefix(
  const abstract_counterexamplet &abstract_counterexample,
  prefixt &prefix,
  goto_symex_statet &state,
  bool constant_propagation)
{
  contextt new_context;
  goto_symext symex_simulator(concrete_model.ns, new_context, prefix.equation);
  symex_simulator.constant_propagation=constant_propagation;
  symex_simulator.options.set_option("assertions", true);
  symex_simulator.options.set_option("all-assertions", true);

  // just concatenate the concrete basic blocks as they
  // are in the abstract counterexample
  
  assert(!abstract_counterexample.steps.empty());

  for(abstract_counterexamplet::stepst::const_iterator
      it=abstract_counterexample.steps.begin();
      it!=abstract_counterexample.steps.end();
      it++)
  {
    if(!it->is_state()) continue;
  
    bool last_state=abstract_counterexample.is_last_step(it);
    
    // get the concrete basic block
    goto_programt::const_targett c_target=it->pc->code.concrete_pc;
    
    if(last_state)
    {
      if(!c_target->is_assert())
        throw "expected assertion at end of abstract trace";
    }
    
    state.source.pc=c_target;
    state.source.thread_nr=it->thread_nr;
    
    unsigned s=prefix.equation.SSA_steps.size();

    switch(c_target->type)
    {
    case GOTO:
      if(it->relevant)
        symex_simulator.symex_step_goto(state, it->branch_taken);
      break;

    case ASSERT:
      if(last_state && it->relevant)
      {
        symex_simulator.symex_step(concrete_model.goto_functions, state);
        assert(prefix.equation.SSA_steps.size()==s+1);
      }
      break;
      
    case DEAD:
    case START_THREAD:
    case END_THREAD:
    case ATOMIC_BEGIN:
    case ATOMIC_END:
      break;

    case RETURN:
      // the usual RETURN branches to the END_FUNCTION
      if(it->relevant)
        symex_simulator.symex_step_return(state);
      break;
      
    case END_FUNCTION:
    default:
      // this one pops the frame
      symex_simulator.symex_step(concrete_model.goto_functions, state);
    }
    
    if(prefix.equation.SSA_steps.size()==s)
    {
      // just note that we have been there
      prefix.equation.location(state.guard, state.source);
    }
    
    // record it
    prefix.record(--prefix.equation.SSA_steps.end(), it);

    // there might be more than one assignment per statement
    //assert(prefix.equation.SSA_steps.size()==s+1);
  }
  
  //prefix.equation.output(std::cout);
  assert(!prefix.equation.SSA_steps.empty());
  assert(prefix.equation.SSA_steps.back().is_assert());
}

/*******************************************************************\

Function: simulator_symext::get_fail_info

  Inputs: 

 Outputs:

 Purpose: Finds the shortest infeasible prefix of prefix

\*******************************************************************/

void simulator_symext::get_fail_info(
  const abstract_counterexamplet &abstract_counterexample,
  const simulator_sat_dect &satcheck,
  const prefixt &prefix,
  const symex_target_equationt::SSA_stepst::const_iterator c_it,
  fail_infot &fail_info)
{
  fail_info.all_steps=abstract_counterexample.steps;

  // this must be an assumption, an assertion or a goto
  assert(c_it->source.pc->is_assert() ||
         c_it->source.pc->is_assume() ||
         c_it->source.pc->is_goto());

  abstract_counterexamplet::stepst::const_iterator a_it=
    prefix.get_abstract_step(c_it);

  fail_info.steps.clear();

  for(abstract_counterexamplet::stepst::const_iterator
      it=abstract_counterexample.steps.begin();
      it!=abstract_counterexample.steps.end();
      it++)
  {
    fail_info.steps.push_back(*it);
    if(it==a_it) break;
  }
      
  fail_info.guard=c_it->source.pc->guard;

  // we might need to negate it
  if(c_it->source.pc->is_goto())
    if(c_it->guard_expr.is_false())
      fail_info.guard.make_not();
}

/*******************************************************************\

Function: simulator_symext::check_prefix_equation

  Inputs: 

 Outputs:

 Purpose: Finds the shortest infeasible prefix of prefix

\*******************************************************************/

bool simulator_symext::check_prefix_equation(
  const abstract_counterexamplet &abstract_counterexample,
  prefixt &prefix,
  goto_symex_statet &state,
  concrete_counterexamplet &concrete_counterexample,
  fail_infot &fail_info)
{
  unsigned int left = 0;     /* leftmost index of search interval  */
  unsigned int right = 0;    /* rightmost index of search interval */
  unsigned int step = 1;     /* the current step size              */
  unsigned int index = 0;    /* the current index into the array   */

  // first of all, that should end with an assertion
  // if not, it's spurious for sure
  
  assert(!prefix.equation.SSA_steps.empty());  
  assert(prefix.equation.SSA_steps.back().is_assert());

  status("Unprocessed prefix of size "+ i2string (prefix.equation.SSA_steps.size ()));

  symex_target_equationt::SSA_stepst::const_iterator c_it;
  
  /* construct an array of iterators (for binary search) */
  std::vector<symex_target_equationt::SSA_stepst::const_iterator> state_array;

  for(c_it=prefix.equation.SSA_steps.begin();
      c_it!=prefix.equation.SSA_steps.end(); 
      c_it++)
  {
    /* assignments and locations don't make a path infeasible */
    if(!(c_it->is_assignment() ||
         c_it->is_location()))
    {
      if(!(c_it->is_assume() && c_it->cond_expr.is_true()))
      {
        state_array.push_back(c_it);

        // this must be an assumption, an assertion or a goto
        assert(c_it->source.pc->is_assert() ||
               c_it->source.pc->is_assume() ||
               c_it->source.pc->is_goto());
      }
    }
  }

  assert(!state_array.empty()); // we expect at least one element!

  status("Processed prefix of size "+ i2string (state_array.size ()));

  right=state_array.size();

  do
  {
    assert(index<state_array.size());
    assert(index>=left);
    assert(index<right);

    status("Simulating prefix of size "+i2string(index+1));

    c_it=state_array[index];
    
    simulator_sat_dect satcheck(concrete_model.ns);
    convert(satcheck, prefix.equation, c_it);

    if(is_satisfiable(satcheck))
    {
      // it's the assertion? grab counterexample!
      if(c_it->is_assert())
      {
        build_goto_trace(
          prefix.equation,
          satcheck,
          concrete_counterexample.goto_trace);

        return false;
      }

      // otherwise decrease the search interval size
      left=index;       /* feasible element      */
    }
    else // unsatisfiable
    {
      right = index;      /* infeasible element    */
      step  = 1;          /* reset the step size   */
      index = left;       /* and restart from left */

      get_fail_info(
        abstract_counterexample,
        satcheck,
        prefix,
        c_it,
        fail_info);
    }
    
    /* now increase the index and the step interval */
    index = 
      (left + step < right)? (left + step) : (right - 1); 

    step = 2 * step;
  }
  while(left+1<right);

  // cannot be simulated, its spurious
  status("Spurious counterexample");

  // report the location
  status("Simulation failed at "+
    fail_info.last_step().pc->location.as_string());
  
  return true;
}

/*******************************************************************\

Function: simulator_symext::check_full_trace

  Inputs: 

 Outputs:

 Purpose: Check if path is feasible

\*******************************************************************/

bool simulator_symext::check_full_trace(
  const abstract_counterexamplet &abstract_counterexample,
  prefixt &prefix,
  goto_symex_statet &state,
  concrete_counterexamplet &concrete_counterexample,
  fail_infot &fail_info)
{
  assert(!prefix.equation.SSA_steps.empty());  
  assert(prefix.equation.SSA_steps.back().is_assert());

  status("Prefix of size "+i2string(prefix.equation.SSA_steps.size()));

  symex_target_equationt::SSA_stepst::const_iterator c_it=
    --prefix.equation.SSA_steps.end();

  simulator_sat_dect satcheck(concrete_model.ns);
  convert(satcheck, prefix.equation, c_it);

  if(is_satisfiable(satcheck))
  {
    // grab counterexample!
    build_goto_trace(
      prefix.equation,
      satcheck,
      concrete_counterexample.goto_trace);

    return false;
  }

  get_fail_info(
    abstract_counterexample,
    satcheck,
    prefix,
    c_it,
    fail_info);
    
  // cannot be simulated, its spurious
  status("Spurious counterexample.");

  return true;
}

/*******************************************************************\

Function: simulator_symext::check_prefix

  Inputs:

 Outputs:

 Purpose: check an abstract counterexample
          Returns TRUE if the counterexample is spurious,
          and FALSE otherwise

\*******************************************************************/

bool simulator_symext::check_prefix(
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
  prefixt prefix(concrete_model.ns);
  goto_symex_statet state;
  state.initialize(concrete_model.goto_functions);

#if 0
  std::cout << "*******************************\n";
  std::cout << abstract_counterexample;
  std::cout << "*******************************\n";
#endif
  
  // turn off constant propagation
  // for the benefit of the refiner
  build_equation_prefix(abstract_counterexample, prefix, state, false);

#if 0
  std::cout << "*******************************\n";
  std::cout << prefix.equation;
  std::cout << "*******************************\n";
#endif
  
  // run decision procedure
  if(shortest_prefix)
    return check_prefix_equation(
      abstract_counterexample,
      prefix,
      state,
      concrete_counterexample,
      fail_info);
  else
    return check_full_trace(
      abstract_counterexample,
      prefix,
      state,
      concrete_counterexample,
      fail_info);  
}

/*******************************************************************\

Function: simulator_symext::is_spurious

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool simulator_symext::is_spurious(
  const predicatest &predicates,
  const abstract_modelt &abstract_model,
  abstract_counterexamplet &abstract_counterexample,
  concrete_counterexamplet &concrete_counterexample,
  fail_infot &fail_info)
{
  status("Simulating abstract counterexample on concrete program");

  #if 0
  std::cout << "***********************************" << std::endl;
  std::cout << abstract_counterexample << std::endl;
  #endif
  
  if(path_slicing)
  {
    #if 0 // buggy right now
    status("Path slicing");
    path_slicer(
      ns,
      abstract_model.goto_functions,
      abstract_counterexample);
    #endif
  }

  #if 0
  std::cout << "***********************************" << std::endl;
  std::cout << abstract_counterexample << std::endl;
  std::cout << "***********************************" << std::endl;
  #endif
  
  if(!check_prefix(
    predicates,
    abstract_model,
    abstract_counterexample,
    concrete_counterexample,
    fail_info))
  {
    status("Simulation successful");
    return false;
  }

  return true;
}
