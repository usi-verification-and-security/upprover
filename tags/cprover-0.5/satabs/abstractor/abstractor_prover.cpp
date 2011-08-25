/*******************************************************************\

Module: Predicate Abstraction of a Basic Block

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include "abstractor_prover.h"
#include "predabs_aux.h"
#include "predicate_image_prover.h"

/*******************************************************************\

Function: abstractor_provert::pred_abstract_block

  Inputs:

 Outputs:

 Purpose: compute abstract transition relation from equation

\*******************************************************************/

void abstractor_provert::pred_abstract_block(
  goto_programt::const_targett target,
  const predicatest &predicates,
  abstract_transition_relationt &
  abstract_transition_relation)
{
  #if 0
  symex_target_equationt equation(ns);
  
  std::vector<exprt> curr_predicates,
                     next_predicates,
                     predicates_wp;
  std::list<exprt> constraints;
  
  build_equation(
    ns,
    predicates,
    concrete_model,
    target,
    constraints,
    equation,
    curr_predicates,
    next_predicates,
    predicates_wp);

  #if 0
  std::cout << equation;
  #endif

  // make them all non-deterministic for now
  for(unsigned i=0; i<predicates.size(); i++)
    abstract_transition_relation.values[i].make_nil();

  // predicate image

  #ifdef HAVE_PROVER
  predicate_image_prover(
    message_handler,
    curr_predicates,
    next_predicates,
    predicates_wp,
    constraints,
    equation,
    ns,
    abstract_transition_relation);
  #else
  throw "no support for prover linked in";
  #endif
  #endif
}

