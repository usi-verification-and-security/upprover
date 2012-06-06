/*******************************************************************\
 
 Module: An inequalities domain invariant

 Author: A. Tsitovich
         CM Wintersteiger
         
\*******************************************************************/

#include "inequalities.h"

/*******************************************************************\
 
 Function: inequalities_invariant_testt::get_invariants

 Inputs:

 Outputs:

 Purpose: Tests for possible equalities

 \*******************************************************************/

void inequalities_invariant_testt::get_invariants(
  const loop_summaryt &summary,
  std::set<exprt> &potential_invariants)
{
  set_operator("<=");
  
  std::set<exprt> temp;
  variable_relations_invariant_testt::get_invariants(summary, temp);
  
  for(std::set<exprt>::const_iterator it=temp.begin();
      it!=temp.end();
      it++)
  {
    exprt t = *it;
    potential_invariants.insert(t);
    t.id(">=");
    potential_invariants.insert(t);
  }
}
