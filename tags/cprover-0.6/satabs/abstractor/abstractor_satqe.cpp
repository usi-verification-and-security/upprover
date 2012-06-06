/*******************************************************************\

Module: Abstractor (generates abstract program given a set of predicates)

Author: Daniel Kroening

  Date: September 2008

\*******************************************************************/

#include "abstractor_satqe.h"
#include "predabs_aux.h"
#include "predicate_image_satqe.h"

/*******************************************************************\

Function: abstractor_satqet::pred_abstract_block

  Inputs:

 Outputs:

 Purpose: compute abstract transition relation from equation

\*******************************************************************/

void abstractor_satqet::pred_abstract_block(
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

  // find unchanged predicates
  // find predicates with value

  for(unsigned i=0; i<predicates.size(); i++)
  {
    if(predicates_wp[i]==predicates[i])
    {
      abstract_transition_relation.values.erase(i);
      //std::cout << "UNCHANGED: P" << i << std::endl;
    }
    else
    {
      #if 0
      std::cout << "DIFFERENT: P" << i << std::endl;
      std::cout << "WP: " << from_expr(ns, "", predicates_wp[i]) << std::endl;
      std::cout << "P:  " << from_expr(ns, "", predicates[i]) << std::endl;
      #endif
      
      abstract_transition_relation.values[i]=
        get_value(i, predicates, predicates_wp[i]);
        
      // if it changes, it's output
      abstract_transition_relation.to_predicates.insert(i);
    }
  }

  // if there is no nondeterministic predicate, we are done
  if(!abstract_transition_relation.has_nondeterminism())
    return;

  #ifdef HAVE_SATQE
  predicate_image_satqe(
    get_message_handler(),
    curr_predicates,
    next_predicates,
    constraints,
    equation,
    ns,
    abstract_transition_relation);
  #else
  throw "no support for satqe linked in";
  #endif
  #endif
}

