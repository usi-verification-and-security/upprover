/*******************************************************************\

Module: Abstractor (generates abstract program given a set of predicates)

Author: Daniel Kroening

  Date: September 2008

\*******************************************************************/

#include "abstractor_wp.h"
#include "predabs_aux.h"

/*******************************************************************\

Function: abstractor_wpt::pred_abstract_block

  Inputs:

 Outputs:

 Purpose: compute abstract transition relation from equation

\*******************************************************************/

void abstractor_wpt::pred_abstract_block(
  goto_programt::const_targett target,
  const predicatest &predicates,
  abstract_transition_relationt &
  abstract_transition_relation)
{
  std::vector<exprt> predicates_wp;

  std::list<exprt> constraints;
  
  build_equation(
    concrete_model.ns,
    predicates,
    target,
    constraints,
    predicates_wp);

  #if 0
  std::cout << target->location << std::endl;
  std::cout << equation;
  #endif

  // find unchanged predicates
  // find predicates with value
  
  for(unsigned i=0; i<predicates.size(); i++)
  {
    if(predicates_wp[i]==predicates[i])
    {
      abstract_transition_relation.values.erase(i);
      #if 0
      std::cout << "UNCHANGED: P" << i << std::endl;
      #endif
    }
    else
    {
      #if 0
      std::cout << "DIFFERENT: P" << i << std::endl;
      std::cout << "WP: " << from_expr(concrete_model.ns, "", predicates_wp[i]) << std::endl;
      std::cout << "P:  " << from_expr(concrete_model.ns, "", predicates[i]) << std::endl;
      #endif
      
      abstract_transition_relation.values[i]=
        get_value(i, predicates, predicates_wp[i]);
        
      // if it changes, it's output
      abstract_transition_relation.to_predicates.insert(i);
    }
  }
}

