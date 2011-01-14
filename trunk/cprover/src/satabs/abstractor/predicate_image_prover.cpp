/*******************************************************************\

Module: Predicate Abstraction of a Basic Block

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <goto-symex/goto_symex_state.h>

#ifdef HAVE_PROVER
#include <prover/symbolic_dec.h>
#endif

#include "predicate_image_prover.h"

/*******************************************************************\

Function: predicate_image_prover

  Inputs:

 Outputs:

 Purpose: compute abstract transition relation from equation

\*******************************************************************/

void predicate_image_prover(
  message_handlert *message_handler,
  const std::vector<exprt> &curr_predicates,
  const std::vector<exprt> &next_predicates,
  const std::vector<exprt> &predicates_wp,
  const std::list<exprt> &constaints,
  const symex_target_equationt &equation,
  const namespacet &ns,
  abstract_transition_relationt &abstract_transition_relation)
{
  if(curr_predicates.empty()) return;

  message_handler->print(9, "********** RUNNING PROVER");

  #ifdef HAVE_PROVER
  symbolic_dect symbolic_dec;
  
  // pass equation to prover
  equation.convert_assignments(symbolic_dec);
  
  // pass predicates to prover

  for(unsigned i=0; i<curr_predicates.size(); i++)
  {
    exprt cond("predicate_symbol", typet("bool"));
    cond.set("identifier", i);
    symbolic_dec.symbolic_fact(curr_predicates[i], cond);
  }

  for(unsigned i=0; i<next_predicates.size(); i++)
  {
    exprt cond("predicate_next_symbol", typet("bool"));
    cond.set("identifier", i);
    symbolic_dec.symbolic_fact(next_predicates[i], cond);

    exprt tmp(predicates_wp[i]);
    goto_symex_statet state;
    state.rename(tmp, ns);
    symbolic_dec.symbolic_fact(tmp, cond);
  }
  
  // run prover
  if(symbolic_dec.dec_solve()!=decision_proceduret::D_SATISFIABLE)
    throw "unexpected result from symbolic_dect";

  // build set to avoid duplicates
  std::set<exprt> expr_set;

  forall_expr_list(it, abstract_transition_relation.constraints)
    expr_set.insert(*it);

  // collect constraints
  const expr_listt &constraints=symbolic_dec.get_constraints();

  forall_expr_list(it, constraints)
    if(expr_set.insert(*it).second)
      abstract_transition_relation.constraints.push_back(*it);
  #else
  assert(false);
  #endif

  message_handler->print(9, "********** PROVER DONE");
}

