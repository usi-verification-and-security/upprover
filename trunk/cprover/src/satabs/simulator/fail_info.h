/*******************************************************************\

Module: Simulator

Author: Daniel Kroening
    
Date: December 2003

Purpose: 

\*******************************************************************/

#ifndef CPROVER_SATABS_FAIL_INFO_H
#define CPROVER_SATABS_FAIL_INFO_H

#include <assert.h>
#include <list>

#include "../modelchecker/abstract_counterexample.h"

class fail_infot
{
public:
  fail_infot():
    use_invariants(false),
    warn_on_failure(true)
  {
  }

  // fragment of abstract counterexample that is responsible
  // for failure
  abstract_counterexamplet::stepst steps;
  abstract_counterexamplet::stepst all_steps;
  
  // guard that's to blame
  exprt guard;

  // Loop detection: is parameterized equation infeasible?
  // if yes, use the loop invariants for refinement
  bool use_invariants;
  // Loop detection: sometimes we _expect_ a refinement
  // failure, we don't want warnings
  bool warn_on_failure;
  
  // induction predicates inferred by loop detection
  class induction_infot {
  public:
    std::list<exprt> predicates;
    std::map<goto_programt::const_targett,code_assignt> instructions;
    std::map<goto_programt::const_targett,exprt> closed_forms;

    exprt parameter;

    bool parameter_reuse;
    
    // determines where the initialization
    // will be inserted
    abstract_programt::targett loop_head;
    abstract_programt::targett loop_entry;
    abstract_programt::targett loop_exit;
    
    abstract_counterexamplet::stepst prefix_steps;
    abstract_counterexamplet::stepst loop_steps;
    abstract_counterexamplet::stepst postfix_steps;
  };

  std::list<induction_infot> induction_infos;

  abstract_stept &last_step()
  {
    assert(!steps.empty());
    return steps.back();
  }

  const abstract_stept &last_step() const
  {
    assert(!steps.empty());
    return steps.back();
  }
};

#endif
