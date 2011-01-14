/*******************************************************************\
  
Module: Predicate Refinement for CEGAR

Author: Daniel Kroening

Date: June 2003
 
\*******************************************************************/

#include <assert.h>
#include <algorithm>

#include <expr_util.h>
#include <std_types.h>
#include <std_expr.h>
#include <simplify_expr.h>

#include <langapi/language_util.h>

#include "../abstractor/predabs_aux.h"
#include "../simulator/simulator_sat_dec.h"
#include "transition_refiner.h"

//#define DEBUG

/*******************************************************************\

Function: transition_refinert::refine

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void transition_refinert::refine(
  predicatest &predicates, 
  abstract_modelt &abstract_model,
  const fail_infot &fail_info)
{
  bool error;

  if(prefix_first)
  {
    error=refine_prefix(
      predicates,
      abstract_model,
      fail_info);

    if(error)
      error=check_transitions(
        predicates,
        abstract_model,
        fail_info);
  }
  else
  {  
    error=check_transitions(
      predicates,
      abstract_model,
      fail_info);

    if(error)
      error=refine_prefix(
        predicates,
        abstract_model,
        fail_info);
  }
  
  if(error)
  {
    // dump the CE
    
    for(abstract_counterexamplet::stepst::const_iterator
        it=fail_info.steps.begin();
        it!=fail_info.steps.end();
        it++)
      std::cout << *it;
    
    std::cout << std::endl;
    
    // dump the predicates
    std::cout << "Predicates:" << std::endl;
    
    for(unsigned p=0; p<predicates.size(); p++)
    {
      std::cout << "P" << p << ": "
                << from_expr(concrete_model.ns, "", predicates[p])
                << std::endl;
      //std::cout << "      " << predicates[p] << std::endl;
      std::cout << std::endl;
    }
    
    throw "refinement failure";
  }
}

/*******************************************************************\

Function: transition_refinert::check_transitions

  Inputs:

 Outputs:

 Purpose: fix spurious transition

\*******************************************************************/

bool transition_refinert::check_transitions(
  const predicatest &predicates, 
  abstract_modelt &abstract_model,
  const fail_infot &fail_info)
{
  status("Checking transitions");

  bool error=true;
  
  abstract_counterexamplet::stepst::const_iterator previous;
    
  bool first_state=true;
  bool first_check=true;

  for(abstract_counterexamplet::stepst::const_iterator
      it=fail_info.steps.begin();
      it!=fail_info.steps.end();
      it++)
  {
    if(!it->is_state())
      continue;

    if(first_state)
      first_state=false;
    else
    {
      if(check_transition(
        predicates,
        *previous, *it, first_check))
        error=false;
    }

    // skip transition if path slicer tells us so
    if(!it->relevant)
    {
      #ifdef DEBUG
      std::cout << "Skipping L" << it->label_nr << std::endl;
      it->output (std::cout);
      #endif

      do
      { 
        it++;
      }
      while(!it->is_state() && it!=fail_info.steps.end());
    }

    if(it==fail_info.steps.end())
      break;
    
    previous=it;
  }
  
  if(error)
    status("Transitions are not spurious");
  else
    status("Found a spurious transition");
  
  return error;
}

/*******************************************************************\

Function: transition_refinert::check_transition

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool transition_refinert::check_transition(
  const predicatest &predicates,
  const abstract_stept &abstract_state_from,
  const abstract_stept &abstract_state_to,
  bool &first_check)
{
  // get the concrete basic block
  const goto_programt::instructiont &c_instruction=
    *abstract_state_from.pc->code.concrete_pc;

  #ifdef DEBUG
  std::cout << "transition_refinert::check_transition_async: "
            << c_instruction.location << std::endl;
  #endif

  #ifdef DEBUG
  std::cout << "checking transition from label L" << 
    abstract_state_from.label_nr << " to label L" << 
    abstract_state_to.label_nr << std::endl;
  #endif

  if(c_instruction.is_skip() ||
     c_instruction.is_location() ||
     c_instruction.is_end_function())
    return false; // ok

  if(c_instruction.is_other() && c_instruction.code.is_nil())
    return false; // ok

  if(!c_instruction.is_other() &&
     !c_instruction.is_function_call() &&
     !c_instruction.is_return() &&
     !c_instruction.is_assign())
    return check_guarded_transition(predicates,
             abstract_state_from,
             abstract_state_to);

  return check_assignment_transition(predicates,
           abstract_state_from,
           abstract_state_to);
}

/*******************************************************************\

Function: transition_refinert::check_assignment_transitions

  Inputs:

 Outputs:

 Purpose: fix spurious assignment transition

\*******************************************************************/

bool transition_refinert::check_assignment_transition(
  const predicatest &predicates,
  const abstract_stept &abstract_state_from,
  const abstract_stept &abstract_state_to)
{
  #ifdef DEBUG
  std::cout << "transition_refinert::check_transition_async 1" << std::endl;
  #endif

  // if all the predicates have fixed values, it can't be wrong
  // unless where we come from an inconsistent state.
  // thus, check the first time
  abstract_transition_relationt &abstract_transition_relation=
    abstract_state_from.pc->code.transition_relation;

  if(!abstract_transition_relation.has_predicates())
  {
    print(9, "no predicates to check");
    return false; // ok
  }
  
  #ifdef DEBUG
  std::cout << "transition_refinert::check_transition_async 2" << std::endl;
  #endif

  if(abstract_transition_relation.is_skip())
  {
    print(9, "Transition is skip");
    return false; // ok
  }

  #ifdef DEBUG
  std::cout << "transition_refinert::check_transition_async 3" << std::endl;
  #endif

  // check cache
  transition_cachet::entryt transition_cache_entry;

  transition_cache_entry.build(
    abstract_state_from,
    abstract_state_to);
  
  if(transition_cache.in_cache(transition_cache_entry))
  {
    print(9, "Transition is in cache");
    return false;
  }

  #ifdef DEBUG
  std::cout << "transition_refinert::check_transition_async 4" << std::endl;
  #endif

  std::vector<exprt> predicates_wp;
  std::list<exprt> constraints;
  
  build_equation(
    concrete_model.ns,
    predicates,
    abstract_state_from.pc->code.concrete_pc,
    constraints,
    predicates_wp);
    
  // create SAT solver object
  satcheckt satcheck;
  bv_pointerst solver(concrete_model.ns, satcheck);
  solver.unbounded_array=boolbvt::U_ALL;
  
  // convert constraints
  for(std::list<exprt>::const_iterator
      it=constraints.begin();
      it!=constraints.end();
      it++)
  {
    exprt tmp(*it);
    solver.set_to_true(tmp);
  }

  // add predicates
  const std::set<unsigned> &from_predicates=
    abstract_transition_relation.from_predicates;

  const std::set<unsigned> &to_predicates=
    abstract_transition_relation.to_predicates;

  std::map<unsigned, literalt>
    predicate_variables_from, predicate_variables_to;
    
  bvt assumptions;

  for(std::set<unsigned>::const_iterator
      it=from_predicates.begin();
      it!=from_predicates.end(); it++)
  {
    unsigned i=*it;

    literalt li=make_pos(concrete_model.ns, solver, predicates[i]);
    predicate_variables_from[i]=li;
    
    assert(abstract_state_from.predicate_values.size()==predicates.size());
    
    assumptions.push_back(li.cond_negation(
      !abstract_state_from.predicate_values[i]));
    
    #ifdef DEBUG
    std::cout
      << "F: P" << i << ": "
      << (abstract_state_from.predicate_values[i]?"":"!") << "(" 
      << from_expr(concrete_model.ns, "", predicates[i]) << ")" << std::endl;
    #endif
  }

  for(std::set<unsigned>::const_iterator
      it=to_predicates.begin();
      it!=to_predicates.end(); it++)
  {
    unsigned i=*it;

    literalt lo=make_pos(concrete_model.ns, solver, predicates_wp[i]);
    predicate_variables_to[i]=lo;

    assert(abstract_state_to.predicate_values.size()==predicates.size());

    assumptions.push_back(lo.cond_negation(
      !abstract_state_to.predicate_values[i]));
    
    #ifdef DEBUG
    std::cout 
      << "T: P" << i << ": " << (abstract_state_to.predicate_values[i]?"":"!") << "("
      << from_expr(concrete_model.ns, "", predicates[i]) << ")" << std::endl;
    #endif
  }
  
  satcheck.set_assumptions(assumptions);
  
  #ifdef DEBUG
  std::cout << "transition_refinert::check_transition_async 5" << std::endl;
  #endif

  // solve it
  if(is_satisfiable(solver))
  {
    transition_cache.insert(transition_cache_entry);
    print(9, "Transition is OK");
    #ifdef DEBUG
    std::cout << "********\n";
    solver.print_assignment(std::cout);
    std::cout << "********\n";
    #endif
    return false; // ok
  }
    
  #ifdef DEBUG
  std::cout << "transition_refinert::check_transition_async 6" << std::endl;
  #endif

  print(9, "Assignment transition is spurious, refining");

  exprt constraint;

  for(std::set<unsigned>::const_iterator
      it=from_predicates.begin();
      it!=from_predicates.end(); it++)
  {
    unsigned i=*it;
    
    if(satcheck.is_in_conflict(predicate_variables_from[i]))
    {
      constraint.operands().push_back(exprt());
      exprt &e=constraint.operands().back();
      e=exprt("predicate_symbol", typet("bool"));
      e.set("identifier", i);
      if(abstract_state_from.predicate_values[i]) e.make_not();
      #if 0
      std::cout << "C: " << from_expr(ns, "", e) << std::endl;
      #endif
    }
  }

  for(std::set<unsigned>::const_iterator
      it=to_predicates.begin();
      it!=to_predicates.end(); it++)
  {
    unsigned i=*it;

    if(satcheck.is_in_conflict(predicate_variables_to[i]))
    {
      constraint.operands().push_back(exprt());
      exprt &e=constraint.operands().back();
      e=exprt("predicate_next_symbol", typet("bool"));
      e.set("identifier", i);
      if(abstract_state_to.predicate_values[i]) e.make_not();
      #if 0
      std::cout << "C: " << from_expr(ns, "", e) << std::endl;
      #endif
    }
  }
  
  if(constraint.operands().empty())
    constraint.make_false(); // this can happen if
  else                       // the invariants are inconsistent
    gen_or(constraint);
  
  abstract_transition_relation.constraints.push_back(constraint);

  // spurious!
  return true;
}

/*******************************************************************\

Function: transition_refinert::check_guarded_transitions

  Inputs:

 Outputs:

 Purpose: fix spurious guarded transition

\*******************************************************************/

bool transition_refinert::check_guarded_transition(
  const predicatest &predicates,
  const abstract_stept &abstract_state_from,
  const abstract_stept &abstract_state_to)
{
  // get the concrete basic block
  const goto_programt::instructiont &c_instruction=
    *abstract_state_from.pc->code.concrete_pc;

  if (!c_instruction.is_goto() &&
      !c_instruction.is_assume())
    return false; // whatever

  // this is the original guard
  exprt guard=c_instruction.guard; 

  if(guard.is_true()) // boring
    return false;

  // we might need to negate it if the branch was not taken
  if (c_instruction.is_goto() && 
      !abstract_state_from.branch_taken)
    guard.make_not();

  abstract_transition_relationt &abstract_transition_relation=
    abstract_state_from.pc->code.transition_relation;

  if(!abstract_transition_relation.has_predicates())
  {
    print(9, "no predicates to check");
    return false; // ok
  }

  #ifdef DEBUG
  std::cout << "transition_refinert::check_guarded_transition 1" << std::endl;
  #endif

  // check cache
  transition_cachet::entryt transition_cache_entry;

  transition_cache_entry.build(
    abstract_state_from,
    abstract_state_to);
  
  if(transition_cache.in_cache(transition_cache_entry))
  {
    print(9, "Transition is in cache");
    return false;
  }

  #ifdef DEBUG
  std::cout << "transition_refinert::check_guarded_transition 2" << std::endl;
  #endif

  satcheckt satcheck;
  bv_pointerst solver(concrete_model.ns, satcheck);

  #ifdef DEBUG
  std::cout << "transition_refinert::check_guarded_transition 3" << std::endl;
  #endif

  // add from predicates, ignore to predicates, since they're not changed
  const std::set<unsigned> &from_predicates=
    abstract_transition_relation.from_predicates;

  std::map<unsigned, literalt> predicate_variables_from;
  
  bvt assumptions;

  for(std::set<unsigned>::const_iterator
      it=from_predicates.begin();
      it!=from_predicates.end(); it++)
  {
    unsigned i=*it;

    literalt li=make_pos(concrete_model.ns, solver, predicates[i]);
    predicate_variables_from[i]=li;
    
    assert(abstract_state_from.predicate_values.size()==predicates.size());

    assumptions.push_back(li.cond_negation(
      !abstract_state_from.predicate_values[i]));
    
    #ifdef DEBUG
    std::cout
      << "F: P" << i << ": " << (abstract_state_from.predicate_values[i]?"":"!") << "(" 
      << from_expr(concrete_model.ns, "", predicates[i]) << ")" << std::endl;
    #endif
  }
  
  satcheck.set_assumptions(assumptions);

  if(!is_satisfiable(solver))
  {
    print(9, "Guarded transition spurious due to invalid abstract state");
    return false; // this has to be fixed in the respective assignment
  }

  // now add the guard
  solver.set_to_true(guard);

  // solve it incrementally
  if(is_satisfiable(solver))
  {
    transition_cache.insert(transition_cache_entry);
    print(9, "Transition is OK");
    #ifdef DEBUG
    std::cout << "********\n";
    solver.print_assignment(std::cout);
    std::cout << "********\n";
    #endif
    return false; // ok
  }
 
  #ifdef DEBUG
  std::cout << "transition_refinert::check_guarded_transition 3" << std::endl;
  #endif

  print(9, "Guarded transition is spurious, refining");

  exprt condition;

  for(std::set<unsigned>::const_iterator
      it=from_predicates.begin();
      it!=from_predicates.end(); it++)
  {
    unsigned i=*it;
      
    if(satcheck.is_in_conflict(predicate_variables_from[i]))
    {
      condition.operands().push_back(exprt());
      exprt &e=condition.operands().back();
      e=exprt("predicate_symbol", bool_typet());
      e.set(ID_identifier, i);
      if(!abstract_state_from.predicate_values[i]) e.make_not();
      #if 0
      std::cout << "C: " << from_expr(concrete_model.ns, "", e) << std::endl;
      #endif
    }
  }

  gen_and(condition);

  if(c_instruction.is_goto())
  {  
    bool neg=abstract_state_from.branch_taken;
    constrain_goto_transition(abstract_transition_relation, condition, neg);
  }
  else
  {
    assert(c_instruction.is_assume());
    constrain_assume_transition(abstract_transition_relation, condition);
  }

  // spurious
  return true;
}

/*******************************************************************\

Function: transition_refinert::constrain_goto_transition

  Inputs:

 Outputs:

 Purpose: add a constraint to a goto transition

\*******************************************************************/

void transition_refinert::constrain_goto_transition(
  abstract_transition_relationt &abstract_transition_relation,
  const exprt &condition,
  bool negated)
{
  if(abstract_transition_relation.constraints.size()==0)
  { 
    exprt schoose("bp_schoose", bool_typet());
    schoose.copy_to_operands(false_exprt(), false_exprt());
    abstract_transition_relation.constraints.push_back(schoose);
  }

  // we are only maintaining ONE constraint here
  assert(abstract_transition_relation.constraints.size()==1);

  exprt &schoose=
    abstract_transition_relation.constraints.front();

  exprt &constraint=negated?(schoose.op1()):(schoose.op0()); 
  
  if(constraint.is_false())
  {
    constraint.id("or");
    constraint.copy_to_operands(false_exprt());
  }

  constraint.copy_to_operands(condition);
}

/*******************************************************************\

Function: transition_refinert::constrain_goto_transition

  Inputs:

 Outputs:

 Purpose: add a constraint to an assume transition

\*******************************************************************/

void transition_refinert::constrain_assume_transition(
  abstract_transition_relationt &abstract_transition_relation,
  const exprt &condition)
{
  exprt negation=condition;
  negation.make_not();
  abstract_transition_relation.constraints.push_back(negation);
}
