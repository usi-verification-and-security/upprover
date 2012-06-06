/*******************************************************************\

Module: Simulator for Prefixes with Loops

Author: Daniel Kroening

Date: January 2006

Purpose:

\*******************************************************************/

//#define DEBUG
#define MAGIC_UPPER_BOUND 65536

#include <replace_expr.h>
#include <simplify_expr.h>
#include <i2string.h>
#include <arith_tools.h>
#include <std_expr.h>

#include <solvers/flattening/sat_minimizer.h>
#include <solvers/sat/pbs_dimacs_cnf.h>

#include <ansi-c/c_types.h>

#include <goto-symex/goto_symex.h>
#include <goto-symex/symex_target_equation.h>
#include <goto-symex/build_goto_trace.h>

#include "simulator_loop_detection.h"
//#include "simulator_sat_dec.h"
#include "recurrence_solver.h"

/*******************************************************************\

Function: simulator_loop_detectiont::check_phase_I_equation

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
  
class pbs_wrappert
{
public:
  pbs_dimacs_cnft satcheck;
};

class simulator_pbs_dect:
  public pbs_wrappert,
  public bv_pointerst
{
public:
  virtual const std::string description()
  { return "Bit vector SAT"; }
  
  explicit simulator_pbs_dect(const namespacet &_ns):
    bv_pointerst(ns, satcheck) { }
};

bool simulator_loop_detectiont::check_phase_I_equation(
  symex_target_equationt &equation,
  goto_symex_statet &state,
  const abstract_counterexamplet &abstract_counterexample,
  concrete_counterexamplet &phase_I_counterexample,
  prefixt::step_mapt &step_map,
  fail_infot &fail_info
)
{
  minimization_listt symbols;

  // run SAT
  symex_target_equationt::SSA_stepst::const_iterator c_it;

  for(c_it=equation.SSA_steps.begin();
      c_it!=equation.SSA_steps.end();
      c_it++)
  {
    if(c_it->is_assignment())
    {
      const exprt &rhs = c_it->rhs;
      recurrence_solver::referenced_parameters (state, rhs, symbols);
      continue;
    }

    if(c_it->is_location() ||
       (c_it->is_assume() && c_it->cond_expr.is_true()))
      continue;
    
    bv_minimizing_dect satcheck(concrete_model.ns);

    convert(satcheck, equation, c_it);

    // solve it
    if(!is_satisfiable(satcheck))
      break; // spurious!

    if(c_it->is_assert()) // we reached the assertion
    {
      for (minimization_listt::const_iterator m_it = symbols.begin();
           m_it!=symbols.end(); m_it++)
        std::cout << from_expr (concrete_model.ns, "", *m_it) << ", ";
      std::cout << std::endl;

      if(!satcheck.minimize (symbols))
        status("Unable to minimize parameters.");
      
      build_goto_trace(
        equation,
        satcheck, phase_I_counterexample.goto_trace);
      
      return false;
    }
  }

  assert(c_it !=equation.SSA_steps.end());

  // cannot be simulated, its spurious
  status("Phase I Counterexample is spurious");

  // fill fail_info
  fail_info.all_steps = abstract_counterexample.steps;

  assert(c_it->source.pc->is_assert() ||
         c_it->source.pc->is_assume() ||
         c_it->source.pc->is_goto());

  // get the corresponding abstract step
  prefixt::step_mapt::const_iterator s_it=step_map.find(c_it);
  assert (s_it!=step_map.end());
  abstract_counterexamplet::stepst::const_iterator a_it = s_it->second;

  // and fill the steps
  fail_info.steps.clear();

  for(abstract_counterexamplet::stepst::const_iterator
      it=abstract_counterexample.steps.begin();
      it!=abstract_counterexample.steps.end();
      it++)
  {
    fail_info.steps.push_back(*it);
    if(it==a_it) 
      break;
  }

  fail_info.guard=c_it->source.pc->guard;

  // we might need to negate it
  if (c_it->source.pc->is_goto())
    if (c_it->guard_expr.is_false())
      fail_info.guard.make_not();

  return true;
}

/*******************************************************************\

Function: simulator_loop_detectiont::build_loop_recurrence

  Inputs:

 Outputs:

 Purpose: Builds the loop recurrences and returns a conjunction
          of refinement predicates in recurrence

\*******************************************************************/

void simulator_loop_detectiont::build_loop_recurrence(
  symex_target_equationt &equation,
  goto_symex_statet &end_state,
  loop_begint &loop_begin,
  const exprt &parameter_expr,
  std::list<exprt> &recurrences,
  std::map<goto_programt::const_targett,code_assignt> &instructions,
  std::map<goto_programt::const_targett,exprt> &closed_forms)
{
  // find start in equation

  symex_target_equationt::SSA_stepst::iterator
    start_it=equation.get_SSA_step(loop_begin.state_nr);

  // build the problem
  
  std::map<exprt, exprt> problem;
  std::set<exprt> start_values, end_values;
    
  for(symex_target_equationt::SSA_stepst::iterator
      e_it=start_it; e_it!=equation.SSA_steps.end(); e_it++)
  {
    symex_target_equationt::SSA_stept &s=*e_it;
    
    if(s.is_assignment())
    {
      const exprt &lhs=s.lhs;
      const exprt &rhs=s.rhs;
 
      // compute start/end values
      start_values.insert(rename(loop_begin.state, s.original_lhs));
      end_values.insert(rename(end_state, s.original_lhs));

      if (!s.original_lhs.get_bool("induction_symbol"))
        {
          problem[lhs]=rhs;      
          #if 0
          std::cout << "Part of the problem: " << 
            from_expr (ns, "", lhs) << " := " << from_expr (ns, "", rhs)
                    << std::endl;
          #endif
        }
    }
  }

  // create a new parameter variable
  loop_infos.push_back(loop_infot());

  loop_infos.back().parameter=parameter_expr;

  // solve the problem

  replace_mapt solution;
  recurrence_solver::solve_recurrence(parameter_expr, 
                                      start_values, 
                                      end_values, 
                                      loop_begin.state,
                                      end_state,
                                      problem, 
                                      solution,
                                      concrete_model.ns);  

  // put in solution

  for(symex_target_equationt::SSA_stepst::iterator
      e_it=start_it; e_it!=equation.SSA_steps.end(); e_it++)
  {
    bool has_recurrence = false;
    symex_target_equationt::SSA_stept &s=*e_it;
    
    #ifdef DEBUG
    std::cout << "*** " << s.pc->location << std::endl;
    #endif
    
    if(s.is_assignment())
    {
      if (solution[s.lhs].id()!="nondet_symbol" && 
          solution[s.lhs] != s.rhs &&
          !s.lhs.get_bool("induction_symbol"))
        has_recurrence = true;

      #ifdef DEBUG
      std::cout << "ASSIGNMENT BEFORE: " << from_expr(ns, "", s.lhs) << " := "
                << from_expr(ns, "", s.rhs) << std::endl;
      #endif

      if (!s.original_lhs.get_bool("induction_symbol"))
        s.rhs=solution[s.lhs];

      #ifdef DEBUG
      std::cout << "ASSIGNMENT AFTER: " << from_expr(ns, "", s.lhs) << " := "
                << from_expr(ns, "", s.rhs) << std::endl;
      #endif

      // fix cond
      assert(s.cond_expr.id()=="=" && s.cond_expr.operands().size()==2);
      s.cond_expr.op1()=s.rhs;

      // remember the recurrence instruction and the
      // closed form for WP computation
      code_assignt instruction(s.lhs, solution[s.lhs]);
      end_state.get_original_name(instruction);
      instructions[s.source.pc] = instruction;
      if(has_recurrence)
      {
        exprt equality=equality_exprt(s.lhs, solution[s.lhs]);
        if(!s.lhs.get_bool("induction_symbol"))
        {
          closed_forms[s.source.pc]=equality;
        }
      }
    }
    else if(s.is_assert())
    {
      #ifdef DEBUG
      std::cout << "ASSERT: " << from_expr(ns, "", s.cond) << std::endl;
      #endif
    }
    else if(s.is_assume())
    {
      #ifdef DEBUG
      std::cout << "ASSUME: " << from_expr(ns, "", s.cond) << std::endl;
      #endif
    }
  }
  
  // assign parameter, so we can grab it from a counterexample
  exprt tmp(parameter_expr);
  equation.assignment(
    guardt(),
    parameter_expr,
    parameter_expr,
    tmp,
    loop_begin.state.source,
    symex_targett::STATE);

  // now clean up the recurrence predicates used for refinement
  recurrence_solver::cleanup_recurrence_predicates(equation,
                                                   loop_begin.state_nr,
                                                   end_state,
                                                   problem, 
                                                   closed_forms,
                                                   recurrences,
                                                   concrete_model.ns);
}

/*******************************************************************\

Function: check_for_induction_variables

  Inputs: The prefix steps and the postfix steps.
          An empty expression set (variables) which
          is used to store the results

 Outputs: A list of induction variables for that trace
          (i.e., a matching variable such that N$x=0 and N$x++
          exists on the corresponding parts of the trace)
          if such a variable already exists

 Purpose: Check for existing induction variables and instructions
          in order to prevent that we add additional ones that 
          are redundant

\*******************************************************************/

void simulator_loop_detectiont::check_for_induction_variables(
    const abstract_counterexamplet::stepst prefix,
    const abstract_counterexamplet::stepst body,
    std::set<exprt>& variables)
{
  // occurences: once, more than once
  std::set<exprt> occ0, occ1;

  // check the body first
  for (abstract_counterexamplet::stepst::const_iterator 
         b_it = body.begin();
       b_it != body.end();
       b_it++)
    {
      if(b_it->is_state())
        {
          goto_programt::const_targett instr=b_it->pc->code.concrete_pc;
          
          // search for N$x = 1 + N$x
          if(instr->is_assign())
            {
              const exprt& lhs = instr->code.op0();
              if (lhs.get_bool("induction_symbol"))
                {
                  const exprt& rhs = instr->code.op1();
                  if (rhs.id()=="+" && rhs.operands().size()==2)
                    {
                      const exprt& increase = rhs.op0();
                      const exprt& param = rhs.op1();
                     
                      if (increase.is_one() && (lhs == param))
                        {
                          // found N$x = 1 + N$x
                          if (occ0.find (lhs) != occ0.end())
                            occ1.insert (lhs);
                          else
                            occ0.insert (lhs);
                        }
                    }
                }
            }
        }
    }

  // now check if a N$x in (occ0\occ1) occurs in the prefix
  std::set<exprt> occ;
  std::insert_iterator<std::set<exprt> >
    o_it (occ, occ.begin());
  
  std::set_difference (occ0.begin(), occ0.end(),
                       occ1.begin(), occ1.end(), o_it);

  for (abstract_counterexamplet::stepst::const_iterator 
         p_it = prefix.begin();
       p_it != prefix.end();
       p_it++)
    {
      if(p_it->is_state())
        {
          goto_programt::const_targett instr=p_it->pc->code.concrete_pc;
          
          // search for N$x = 0
          if(instr->is_assign())
            {
              const exprt& lhs = instr->code.op0();
              if (lhs.get_bool("induction_symbol"))
                {
                  if (occ.find (lhs) != occ.end())
                    {
                      const exprt& rhs = instr->code.op1();
                       
                      if (rhs.is_zero())
                        variables.insert (lhs);
                    }
                }
            }
        }
    }
}

/*******************************************************************\

Function: fill_induction_info

  Inputs: The abstract counterexample, the start and end iterators of the
          loop, the parameter N, and the ouptut induction_infot
          structure

 Outputs: A filled loop_infot structure

 Purpose: Generates the induction_info structure for the current loop
          and finds a new induction variable

\*******************************************************************/

void simulator_loop_detectiont::fill_loop_info(
  const abstract_counterexamplet &abstract_counterexample,
  const abstract_counterexamplet::stepst::const_iterator start_it,
  const abstract_counterexamplet::stepst::const_iterator end_it,
  fail_infot::induction_infot &induction_info)
{
  // get head of loop
  abstract_counterexamplet::stepst::const_iterator head = start_it;
  head++;
  assert (head->has_pc);
  induction_info.loop_head = head->pc;

  // get first statement in loop
  head++;
  assert (head->has_pc);
  induction_info.loop_entry = head->pc;

  // get last statement of loop
  abstract_counterexamplet::stepst::const_iterator last = end_it;
  last--;
  assert (last->has_pc);
  induction_info.loop_exit = last->pc;

  // fill the steps information
  abstract_counterexamplet::stepst::const_iterator s_it;

  for (s_it = abstract_counterexample.steps.begin(); 
       s_it != start_it; s_it++)
    {
      induction_info.prefix_steps.push_back(*s_it);
    }

  s_it = start_it;
  for (s_it++; s_it != end_it; s_it++)
    {
      induction_info.loop_steps.push_back(*s_it);
    }

  s_it = end_it;
  for (s_it++; 
       s_it != abstract_counterexample.steps.end();
       s_it++)
    {
      induction_info.postfix_steps.push_back(*s_it);
    }

  // now find an induction parameter
  std::set<exprt> induction_vars;

  check_for_induction_variables (induction_info.prefix_steps,
                                 induction_info.loop_steps,
                                 induction_vars);

  if (induction_vars.size()!=0)
    {
      induction_info.parameter = *induction_vars.begin(); 
      induction_info.parameter_reuse = true;

#ifdef DEBUG
      std::cout << "Reusing induction parameter " << 
        from_expr (ns, "", induction_info.parameter) << std::endl;
#endif
    }
  else
    {
      get_fresh_induction_parameter(induction_info.parameter);
      induction_info.parameter_reuse = false;
    }
}



/*******************************************************************\

Function: simulator_loop_detectiont::get_fresh_induction_parameter

  Inputs:

 Outputs: A fresh parameter expression

 Purpose: Generate a fresh variable that is used as 
          parameter for the loop recurrence

\*******************************************************************/

void simulator_loop_detectiont::get_fresh_induction_parameter(
  exprt &parameter)
{
  exprt parameter_expr("symbol", uint_type());

  bool found;
  do 
    {
      parameter_index++;
      parameter_expr.set("identifier", "c::N$"+i2string(parameter_index));
      parameter_expr.set("induction_symbol", true);

      try 
        {
          concrete_model.ns.lookup(parameter_expr);
          found = true;
        }
      catch (std::string ex) 
        {
          found = false;
        }
    }
  while (found);

  symbolt sym;

  sym.name = parameter_expr.get("identifier");
  sym.base_name = (irep_idt)("N$"+i2string(parameter_index));
  sym.module = (irep_idt)"c";

  shadow_context.add (sym);
  
  parameter = parameter_expr;
}


/*******************************************************************\

Function: simulator_loop_detectiont::build_parameterized_equation

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void simulator_loop_detectiont::build_parameterized_equation(
  const abstract_counterexamplet &abstract_counterexample,
  symex_target_equationt &equation,
  goto_symex_statet &state,
  fail_infot &fail_info,
  prefixt::step_mapt &step_map)
{
  contextt new_context;
  goto_symext symex_simulator(concrete_model.ns, new_context, equation);
  loop_stackt loop_stack;

  // turn off constant propagation -- it's not sound here
  symex_simulator.constant_propagation=false;
  
  // for ignoring nested ones
  bool ignore=false;



  for(abstract_counterexamplet::stepst::const_iterator
      it=abstract_counterexample.steps.begin();
      it!=abstract_counterexample.steps.end();
      it++)
  {
    if(it->is_state())
    {
      bool last_state=(it==--abstract_counterexample.steps.end());

      // get the concrete basic block
      goto_programt::const_targett c_target=it->pc->code.concrete_pc;
      
      if(last_state)
      {
        if(!c_target->is_assert())
          throw "expected assertion at end of abstract trace";
      }
      
      state.source.pc=c_target;
      state.source.thread_nr=it->thread_nr;
      
      unsigned s=equation.SSA_steps.size();

      switch(c_target->type)
      {
      case GOTO:
        symex_simulator.symex_step_goto(state, it->branch_taken);
        break;

      case ASSERT:
        if(last_state) 
        {
          goto_functionst goto_functions;
          symex_simulator.symex_step(goto_functions, state);
        }
        break;
        
      case DEAD:
      case START_THREAD:
      case END_THREAD:
      case END_FUNCTION:
        break;

      default:
        {
          goto_functionst goto_functions;
          symex_simulator.symex_step(goto_functions, state);
        }
      }
      
      if(equation.SSA_steps.size()==s)
      {
        // just note that we have been there
        equation.location(state.guard, state.source);
      }

      // record it (as in simulator_symext::build_equation_prefix)
      step_map[--equation.SSA_steps.end()] = it;

    }
    else if(it->is_loop_begin())
    {
      // remember where we started
      loop_stack.push(loop_begint());
      loop_stack.top().state_nr=equation.SSA_steps.size();
      loop_stack.top().state=state;
      loop_stack.top().c_it = it;
      ignore=false;
    }
    else if(it->is_loop_end())
    {
      assert(!loop_stack.empty());

      fail_infot::induction_infot induction_info;

      // fill in steps and find new parameter
      fill_loop_info (abstract_counterexample,
                      loop_stack.top().c_it,
                      it,
                      induction_info);      

      // predicate inferred by recurrences
      std::list<exprt> loop_predicates;

      build_loop_recurrence(equation, state, 
                            loop_stack.top(), 
                            induction_info.parameter,
                            induction_info.predicates,
                            induction_info.instructions,
                            induction_info.closed_forms);

      // now add the recurrences to fail_info
      if (induction_info.predicates.size())
        fail_info.induction_infos.push_back (induction_info);
      
      loop_stack.pop();
      ignore=true;
    }
    else
      assert(false);
  }

  #ifdef DEBUG
  equation.output(std::cout);
  #endif
}

/*******************************************************************\

Function: simulator_loop_detectiont::unwind_counterexample

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void simulator_loop_detectiont::unwind_counterexample(
  const abstract_counterexamplet &abstract_counterexample,
  const concrete_counterexamplet &phase_I_counterexample,
  abstract_counterexamplet &unwound_counterexample)
{
  //
  //  get the parameters from the concrete counterexample
  //

  for(loop_infost::iterator l_it=loop_infos.begin();
      l_it!=loop_infos.end();
      l_it++)
  {
    bool found=false;

    for(goto_tracet::stepst::const_iterator s_it=
        phase_I_counterexample.goto_trace.steps.begin();
        s_it!=phase_I_counterexample.goto_trace.steps.end();
        s_it++)
    {
      if(s_it->original_lhs==l_it->parameter)
      {
        assert(!to_integer(s_it->value, l_it->parameter_value));
        found=true;
        break;
      }
    }
    
    assert(found);
  
    #ifdef DEBUG
    std::cout << "PARAMETER " << from_expr(ns, "", l_it->parameter)
              << " = " << l_it->parameter_value << std::endl;
    #endif
  }

  //
  // build phase II counterexample
  //
  
  unwound_counterexample.steps.clear();

  loop_stackt loop_stack;
  loop_headst loop_heads;

  for(abstract_counterexamplet::stepst::const_iterator
      it=abstract_counterexample.steps.begin();
      it!=abstract_counterexample.steps.end();
      it++)
  {
    if(it->is_state())
    {
      unwound_counterexample.steps.push_back(*it);
    }
    else if(it->is_loop_begin())
    {
      // remember where we started
      loop_stack.push(loop_begint());
      mp_integer N;

      // check if we visit this loop head the first time
      loop_headst::const_iterator h_it;

      for (h_it = loop_heads.begin (); h_it != loop_heads.end (); h_it++)
        {
          if (h_it->first == it)
            {
              N = h_it->second;
              break;
            }
        }
      if (h_it == loop_heads.end ())
        {
          assert(!loop_infos.empty());
          N=loop_infos.front().parameter_value;
          loop_infos.pop_front();

          loop_heads.push_back(loop_headt (it, N));
        }

      if(N==0||N>MAGIC_UPPER_BOUND) N=1;

      loop_stack.top().unwindings= N-1;
      loop_stack.top().c_it=it;
    }
    else if(it->is_loop_end())
    {
      assert(!loop_stack.empty());

      if(loop_stack.top().unwindings==0)
      {
        loop_stack.pop();
      }
      else
      {
        // do another iteration: the previous step must have
        // been a goto
        
        assert(!unwound_counterexample.steps.empty());
        abstract_stept &step=unwound_counterexample.steps.back();
        
        assert(step.is_state());
        assert(step.pc->is_goto());
        
        // count down
        --loop_stack.top().unwindings;

        // find out if it needs to be taken or not
        abstract_counterexamplet::stepst::const_iterator
          loop_target=loop_stack.top().c_it;

        abstract_counterexamplet::stepst::const_iterator
          next=it;
        next++;

        // we need to jump if next!=loop_target
        step.branch_taken=(next!=loop_target);
      
        it=loop_target;
      }
    }
    else
      assert(false);
  }
  
  #ifdef DEBUG
  std::cout << unwound_counterexample;
  #endif
}

/*******************************************************************\

Function: simulator_loop_detectiont::check_prefix

  Inputs:

 Outputs:

 Purpose: check an abstract counterexample
          Returns TRUE if the counterexample is spurious,
          and FALSE otherwise

\*******************************************************************/

bool simulator_loop_detectiont::check_prefix(
  const predicatest &predicates,
  const abstract_modelt &abstract_model,
  abstract_counterexamplet &abstract_counterexample,
  concrete_counterexamplet &concrete_counterexample,
  fail_infot &fail_info)
{
  assert(abstract_counterexample.steps.size()!=0);

  // no loop? Do normal stuff.
  if(!abstract_counterexample.has_loops())
    return simulator_symext::check_prefix(
      predicates,
      abstract_model,
      abstract_counterexample,
      concrete_counterexample,
      fail_info);

  // clean up
  concrete_counterexample.clear();
  loop_infos.clear();

  // phase 1: build parameterized equation

  status("Loop Simulation Phase I");
  
  concrete_counterexamplet phase_I_counterexample;

  {  
    // build equation
    symex_target_equationt equation(concrete_model.ns);
    goto_symex_statet state;
    prefixt::step_mapt step_map;

    build_parameterized_equation(abstract_counterexample, 
                                 equation, state,
                                 fail_info, step_map);

    // now we have all recurrence predicates in refinement_infos
#ifdef DEBUG
    std::list<fail_infot::induction_infot>::const_iterator it;
    for (it = fail_info.induction_infos.begin(); 
         it != fail_info.induction_infos.end(); it++)
    {
      const std::list<exprt> &predicates = it->predicates;

      std::cout << "Induction predicate(s): ";
      for (std::list<exprt>::const_iterator p_it = predicates.begin ();
           p_it != predicates.end (); p_it++)
        {
          const exprt &pred = *p_it;
          std::cout << from_expr(ns, "", pred);

          std::list<exprt>::const_iterator next = p_it; next++;
          if (next != predicates.end ())
            std::cout << ", ";
        }
      std::cout << std::endl;
    }

    std::cout << "LOOP_INFO size: " << loop_infos.size () << std::endl;
#endif

    // run decision procedure
    if(check_phase_I_equation(equation, state, 
                              abstract_counterexample, 
                              phase_I_counterexample, 
                              step_map, fail_info))
      {
        fail_info.use_invariants = true;
        return true; // spurious
      }

    // it could still be spurious
    fail_info.use_invariants = false;
  }
  
  // phase 2: unwind counterexample

  status("Loop Simulation Phase II");
  
  #ifdef DEBUG
  std::cout << abstract_counterexample;
  #endif

  {  
    abstract_counterexamplet unwound_counterexample;
    
    unwind_counterexample(
      abstract_counterexample,
      phase_I_counterexample,
      unwound_counterexample);

    unwound_counterexample.swap(abstract_counterexample);

    return simulator_symext::check_prefix(
      predicates,
      abstract_model,
      abstract_counterexample,
      concrete_counterexample,
      fail_info);
  }
}
