/*******************************************************************\
  
Module: Predicate Refinement for CEGAR

Author: Daniel Kroening

Date: June 2003
 
\*******************************************************************/

#include <assert.h>
#include <iostream>

#include <expr_util.h>
#include <arith_tools.h>
#include <i2string.h>

#include <goto-symex/precondition.h>
#include <goto-symex/postcondition.h>
#include <goto-symex/basic_symex.h>

#include <simplify_expr.h>

#include "refiner_wp.h"
#include "substitute_invariants.h"

//#define DEBUG

/*******************************************************************\

Function: refiner_wpt::push_induction_info

  Inputs:

 Outputs:

 Purpose: push the induction_info data structure that
          corresponds to the loop that we enter onto
          the stack

\*******************************************************************/

void refiner_wpt::push_induction_info(
  const fail_infot &fail_info,
  abstract_counterexamplet::stepst::const_iterator c_it,
  std::list<fail_infot::induction_infot> &info_stack
  )
{
  assert (fail_info.use_invariants);
  assert (c_it->is_loop_end());

  // find out which loop we are in

  c_it--; // we are at a loop exit point, so find next program location
  assert (c_it->has_pc);

  std::list<fail_infot::induction_infot>::const_iterator r_it;
  
  for (r_it = fail_info.induction_infos.begin();
       r_it != fail_info.induction_infos.end ();
       r_it++)
    {
      if (r_it->loop_exit==c_it->pc)
        {
#ifdef DEBUG
          std::cout << "Computing loop invariant for loop ending at " 
                    << c_it->pc->location << std::endl;
#endif
          break;
        }
    }

  // remember the induction_info structure
  assert (r_it != fail_info.induction_infos.end());
  const fail_infot::induction_infot &induction_info = *r_it;
  
  info_stack.push_back (induction_info);
}


/*******************************************************************\

Function: refiner_wpt::get_recurrence

  Inputs:

 Outputs:

 Purpose: Returns the recurrence for an assignment at a 
          program location (if such a recurrence exists)

\*******************************************************************/

bool refiner_wpt::get_recurrence(
  const goto_programt::const_targett &concrete_pc,
  const std::list<fail_infot::induction_infot> &info_stack,
  exprt &recurrence)
{
  if (info_stack.size())
    {
      const fail_infot::induction_infot 
        &induction_info=info_stack.back();
      
      std::map<goto_programt::const_targett,
        exprt>::const_iterator 
        c_it=induction_info.closed_forms.find(concrete_pc);
      
      if (c_it!=induction_info.closed_forms.end())
        {
          recurrence=c_it->second;
          return true;
        }
    }
  return false;
}

/*******************************************************************\

Function: refiner_wpt::get_instruction

  Inputs:

 Outputs:

 Purpose: Returns a nondeterministic assignment for
          an instruction for which a recurrence exists.
          The corresponding constraint for the assigned induction
          is added to the invariant

\*******************************************************************/

bool refiner_wpt::get_instruction(
  const goto_programt::const_targett &concrete_pc,
  const std::list<fail_infot::induction_infot> &info_stack,
  codet &instruction,
  exprt &invariant)
{
  exprt recurrence;
  
  if (get_recurrence(concrete_pc, info_stack, recurrence))
    {
      const fail_infot::induction_infot 
        &induction_info=info_stack.back();
      
      std::map<goto_programt::const_targett,
        code_assignt>::const_iterator 
        c_it=induction_info.instructions.find(concrete_pc);
      
      assert (c_it!=induction_info.instructions.end());
      
      instruction=c_it->second;

      // now overwrite the rhs with a non-deterministic value
      exprt nondet("nondet_symbol", instruction.op1().type());
      nondet.set(
        "identifier", 
        "loop$"+instruction.op0().get_string("identifier")+"_"+
        i2string(info_stack.size()));
      instruction.op1().swap(nondet);

      // add the corresponding constraint for this induction
      // variable to the invariant
      exprt conjunct("and", typet("bool"));
      conjunct.operands().resize(2);
      conjunct.op0().swap(recurrence);
      conjunct.op1().swap(invariant);
      invariant.swap(conjunct);
      
      return true;
    }
  return false;
}

/*******************************************************************\

Function: initialize_from_to_predicates

  Inputs: The loop head and the loop exit targett

 Outputs: 

 Purpose: used to initialize the from_predicates and to_predicates
          data structures. Initializes the from and two predicate
          sets with empty sets if they do not already exist

\*******************************************************************/

void refiner_wpt::initialize_from_to_predicates(
  const abstract_programt::targett head,
  const abstract_programt::targett exit)
{
  if (from_predicates.find (head) ==
      from_predicates.end())
    {
      from_predicates[head] = std::set<exprt>();
    }
  
  if (from_predicates.find (exit) ==
      from_predicates.end())
    {
      from_predicates[exit] = std::set<exprt>();
    }
  
  if (to_predicates.find (head) ==
      to_predicates.end())
    {
      to_predicates[head] = std::set<exprt>();
    }
  
  if (to_predicates.find (exit) ==
      to_predicates.end())
    {
      to_predicates[exit] = std::set<exprt>();
    }
}

/*******************************************************************\

Function: refiner_wpt::add_induction_predicates

  Inputs: The abstract model, the fail_info data structure
          filled with loop/induction predicates, and the
          current set of predicates

 Outputs: predicates are augmented with induction predicates,
          induction instructions (N=0, N=N+1) are added to
          the concrete model, and corresponding skip instructions
          to the abstract model

 Purpose: 

\*******************************************************************/

void refiner_wpt::add_induction_predicates(
    const fail_infot &fail_info,
    abstract_modelt &abstract_model,
    predicatest &predicates)
{
  from_predicates.clear ();
  to_predicates.clear();

  std::list<fail_infot::induction_infot>::const_iterator r_it;
  
  for (r_it = fail_info.induction_infos.begin();
       r_it != fail_info.induction_infos.end ();
       r_it++)
    {
      const fail_infot::induction_infot &induction_info = *r_it;
      const std::list<exprt> &induction_preds = induction_info.predicates;
      const exprt &parameter = induction_info.parameter;

      // initialize from_ and to_predicates, if necessary
      initialize_from_to_predicates (
        induction_info.loop_head,
        induction_info.loop_exit);
      
      // we'll treat the predicates as huge conjunction
      exprt predicate = exprt ("and", typet("bool"));

      for (std::list<exprt>::const_iterator p_it = 
             induction_preds.begin();
           p_it != induction_preds.end(); p_it++)
        {
          predicate.copy_to_operands (*p_it);
        }
      
      // since the induction transitions have not been added to 
      // the model yet, we compute the preconditions of N=0
      // and N=N+1 manually. This is much easier than adding
      // the corresponding abstract steps to the counterexample!

      // construct parameter + 1: The induction step
      exprt induction = predicate;

      exprt plus = exprt ("+", parameter.type());
      plus.copy_to_operands (from_integer (1, parameter.type()), parameter);
      replace_expr (parameter, plus, induction);

      // and once more with N substituted by 0: The base case!
      exprt base = predicate;
      replace_expr (parameter, from_integer (0, parameter.type()), base);

      // now build a "fake" fail_info data structure and re-use
      // refine_prefix_async to add our predicates
      fail_infot fake_fail_info;

      // just to make this explicit:
      fake_fail_info.use_invariants = false; 
      // we don't want error messages
      fake_fail_info.warn_on_failure = false;

      // prefix
      fake_fail_info.guard = base;
      fake_fail_info.all_steps = fail_info.all_steps;
      fake_fail_info.steps = induction_info.prefix_steps;

      refine_prefix(predicates, abstract_model, fake_fail_info);

      // loop
      fake_fail_info.guard = induction;
      fake_fail_info.steps = induction_info.loop_steps;

      refine_prefix(predicates, abstract_model, fake_fail_info);

      // postfix
      fake_fail_info.guard = predicate;
      fake_fail_info.steps = induction_info.postfix_steps;
      
      refine_prefix(predicates, abstract_model, fake_fail_info);

      // save predicates for instructions that we'll add later
      from_predicates[induction_info.loop_head].insert(base);
      to_predicates[induction_info.loop_head].insert(predicate);

      from_predicates[induction_info.loop_exit].insert(induction);
      to_predicates[induction_info.loop_exit].insert(predicate);
    }

  // now add the corresponding induction instructions
  add_induction_transitions(fail_info, abstract_model, predicates);
}


/*******************************************************************\

Function: refiner_wpt::add_induction_instruction

  Inputs: An abstract target location, the abstract model,
          and an expression representing the concrete 
          instruction to be inserted. The FROM and the
          TO predicate for the instruction that is added.

 Outputs: concrete_instruction is destroyed

 Purpose: adds a concrete instruction in the concrete model
          at the location that corresponds to the target location
          in the abstract model. The abstract model is also
          updated: a skip is inserted a the corresponding position

\*******************************************************************/

void refiner_wpt::add_induction_instruction(
    const abstract_programt::targett target,
    exprt &concrete_instruction,
    abstract_modelt &abstract_model,
    predicatest &predicates)
{
  #if 0
  // get the targett for the concrete program
  // use a nasty trick to get rid of the const modifier
  const goto_programt::instructionst::iterator &concrete_pc=
    *((const goto_programt::instructionst::iterator*)
      &(target->code.concrete_pc));
  
  goto_programt::targett instruction=
    concrete_model.goto_program.insert(concrete_pc);
  
  instruction->type=ASSIGN;

  instruction->code.swap(concrete_instruction);
  //  instruction->location = target->location;

  abstract_programt::instructionst::iterator skip = 
    abstract_model.goto_program.insert(target);

  // we need to abstract this
  skip->code.re_abstract = true;
  skip->type = instruction->type;
  skip->code.concrete_pc = instruction;
  skip->event = instruction->event;
  skip->location = target->location;

  // get the from and to predicates
  std::set<exprt> &from = from_predicates[target];
  std::set<exprt> &to = to_predicates[target];

  bool found_new = false;
  std::set<exprt>::const_iterator p_it;

  // now add them to our new instruction
  for (p_it = from.begin(); p_it != from.end(); p_it++)
    add_predicates(skip, predicates, *p_it, found_new, FROM);

  for (p_it = to.begin(); p_it != to.end(); p_it++)
    add_predicates(skip, predicates, *p_it, found_new, TO);
      
  abstract_model.goto_program.update();

  /* now update pointer analysis information                   */
  /* our new instructions don't change anything (I assume ;-)) */
  concrete_model.value_set_analysis.insert(instruction);
  
  goto_programt::targett next_instruction = instruction;
      
  next_instruction++;
  assert (concrete_model.value_set_analysis.has_location(next_instruction));

  concrete_model.value_set_analysis[instruction] =
    concrete_model.value_set_analysis[next_instruction];

  /* we'll add an empty invariant set */
  concrete_model.invariant_propagation.insert(instruction);

  concrete_model.goto_program.update();
  #endif
}

/*******************************************************************\

Function: refiner_wpt::add_induction_transitions

  Inputs:

 Outputs:

 Purpose: adds initialization assignments for the freshly 
          introduced induction variables to the abstract 
          program as well as to the concrete program

\*******************************************************************/

void refiner_wpt::add_induction_transitions(
  const fail_infot &fail_info,
  abstract_modelt &abstract_model,
  predicatest &predicates)
{
  std::list<fail_infot::induction_infot>::const_iterator it;

  for (it = fail_info.induction_infos.begin();
       it != fail_info.induction_infos.end();
       it++)
  {
    const fail_infot::induction_infot &info = (*it);

    if (info.parameter_reuse)
      continue;

    // insert N := 0
    code_assignt initialize(
      info.parameter,
      gen_zero(info.parameter.type()));

    // compute from and to predicates
    
    add_induction_instruction(
      info.loop_head, 
      initialize,
      abstract_model,
      predicates);

    // insert N := N + 1

    exprt successor = exprt ("+", info.parameter.type());
    successor.copy_to_operands (
      from_integer (1, info.parameter.type()), info.parameter);

    code_assignt increase(info.parameter, successor);
    
    add_induction_instruction(
      info.loop_exit, 
      increase, 
      abstract_model,
      predicates);
  }
}


