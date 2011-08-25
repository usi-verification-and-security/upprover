/*******************************************************************\
  
Module: Predicate Refinement for CEGAR

Author: Daniel Kroening

Date: June 2003
 
\*******************************************************************/

#include <assert.h>
#include <iostream>

#include <expr_util.h>
#include <std_expr.h>
#include <arith_tools.h>
#include <i2string.h>

#include <goto-programs/wp.h>
#include <goto-symex/basic_symex.h>

#include <simplify_expr.h>

#include "refiner_wp.h"

//#define DEBUG

/*******************************************************************\

Function: refiner_wpt::refine_prefix

  Inputs:

 Outputs:

 Purpose: generate a new set of predicates given
          a spurious counterexample

\*******************************************************************/

bool refiner_wpt::refine_prefix(
  predicatest &predicates, 
  abstract_modelt &abstract_model,
  const fail_infot &fail_info)
{
  status("Refining set of predicates according to counterexample (WP)");

  bool found_new=false;

  // keep track of the loops that we're in (may be nested)
  std::list<fail_infot::induction_infot> loops;
  exprt invariant;
  if(fail_info.use_invariants)
    status("Using recurrence predicates detected by loop detection.");
  
  #ifdef DEBUG
  std::cout << "refiner_wpt::refine_prefix_async 1\n";
  #endif
  
  #ifdef DEBUG
  std::cout << "Inconsistent prefix:\n";

  for(abstract_counterexamplet::stepst::const_reverse_iterator 
      r_it=fail_info.steps.rbegin();
      r_it!=fail_info.steps.rend();
      r_it++)
  {
    abstract_programt::targett abstract_pc=r_it->pc;

    goto_programt::const_targett concrete_pc=
      abstract_pc->code.concrete_pc;

    if(concrete_pc->is_goto())
      std::cout << "GUARD: " << (r_it->branch_taken?"(":"!(")
                << from_expr(concrete_model.ns, "", concrete_pc->guard) << ")" << std::endl;
    else if(concrete_pc->is_assert())
      std::cout << "ASSERT: "
                << from_expr(concrete_model.ns, "", concrete_pc->guard) << std::endl;
    else if(concrete_pc->is_location())
      std::cout << "LOC" << std::endl;
    else if(concrete_pc->is_other() || concrete_pc->is_assign() || concrete_pc->is_decl())
      std::cout << from_expr(concrete_model.ns, "", concrete_pc->code) << std::endl;
    else
    {
      std::cout << concrete_pc->type << std::endl;
    }
    std::cout << "**********\n";    
  }

  #endif
  
  {
    // get the constraint causing the failure

    exprt predicate=fail_info.guard;

    #ifdef DEBUG
    std::cout << "P start0: " 
              << from_expr(concrete_model.ns, "", predicate) << std::endl;
    #endif

    simplify(predicate, concrete_model.ns);

    abstract_counterexamplet::stepst::const_iterator 
      it=--fail_info.steps.end();

    // there must be at least two steps, or it's odd
    assert(it!=fail_info.steps.begin());

    {
      abstract_programt::targett abstract_pc=it->pc;

      #ifdef DEBUG
      std::cout << "P start1: " 
                << from_expr(concrete_model.ns, "", predicate) << std::endl;
      #endif

      add_predicates(
        abstract_pc, predicates, predicate, found_new, FROM);
    }
      
    // now do the WPs

    for(it--; // skip last instruction
        it!=fail_info.steps.begin();
        it--)
    {
      #ifdef DEBUG
      std::cout << "refiner_wpt::refine_prefix_async 2\n";
      #endif

      // handle loops 
      if(fail_info.use_invariants)
      {
        if(it->is_loop_begin())
        {
          loops.pop_back(); // pop induction_info if we leave loop
          
#ifdef DEBUG
          std::cout << "INV: "
                    << from_expr(concrete_model.ns, "", invariant) << std::endl;
#endif           
          
          exprt wp(ID_and, typet(ID_bool));
          wp.operands().resize(2);
          wp.op0().swap(invariant);
          wp.op1().swap(predicate);
          predicate.swap(wp);
        }
        else if (it->is_loop_end())
        {
          push_induction_info(fail_info, it, loops);
          invariant.make_true();
        }
      }

      if(!it->is_state())
        continue;

      if(predicate.is_true() && found_new)
      {
        // ok, refuted it, done
        break;
      }
        
      // add the predicate

      goto_programt::const_targett concrete_pc=
        it->pc->code.concrete_pc;
        
      abstract_programt::targett abstract_pc=it->pc;
        
      #ifdef DEBUG
      std::cout << from_expr(concrete_model.ns, "", predicate) << std::endl;
      #endif
      
      add_predicates(abstract_pc, predicates, predicate, found_new, TO);

      // skip irrelevant instructions
      if(!it->relevant) continue;

      // compute weakest precondition
      switch(it->pc->type)
      {
      case ASSUME:
        // we only do this for assumptions
        // if we haven't found a new predicate so far
        if(!found_new)
        {
          predicate=implies_exprt(concrete_pc->guard, predicate);
          simplify(predicate, concrete_model.ns);
        }
        break;

      case GOTO:
        {
          exprt guard=concrete_pc->guard;
          if(!it->branch_taken) guard.make_not();
          predicate=implies_exprt(guard, predicate);
          simplify(predicate, concrete_model.ns);
        }
        break;

      case OTHER:
      case ASSIGN:
        #ifdef DEBUG
        std::cout << "OTHER/ASSIGN\n";
        #endif

        {
          codet tmp_code;
          if(!fail_info.use_invariants ||
             !get_instruction(concrete_pc, loops, tmp_code, invariant))
            tmp_code=to_code(concrete_pc->code);

#ifdef DEBUG
          std::cout << "A P before: " << from_expr(concrete_model.ns, "", predicate) << std::endl;
          std::cout << "Code:     " << from_expr(concrete_model.ns, "", tmp_code) << std::endl;
#endif
          
          // compute weakest precondition
          exprt predicate_wp=wp(tmp_code, predicate, concrete_model.ns);
      
          simplify(predicate_wp, concrete_model.ns);
          predicate=predicate_wp;

#ifdef DEBUG
          std::cout << "A P after:  " << from_expr(concrete_model.ns, "", predicate) << std::endl;
#endif
        }
        break;

      default:
        // ignore
        break;
      }
      
      #ifdef DEBUG
      std::cout << "B P after:   " << from_expr(concrete_model.ns, "", predicate) << std::endl;
      #endif

      add_predicates(abstract_pc, predicates, predicate, found_new, FROM);
    }

    if(!predicate.is_true() && fail_info.warn_on_failure)
    {
      warning("Failed to refute spurious trace with WPs (got "+
              from_expr(concrete_model.ns, "", predicate)+")");
    }
  }

  if(found_new && fail_info.use_invariants)
  {
    add_induction_predicates(
      fail_info,
      abstract_model,
      predicates);
  }
  
  // make sure we have progress
  return !found_new;
}
