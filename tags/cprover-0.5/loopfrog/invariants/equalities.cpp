/*******************************************************************\
 
 Module: An equalities domain invariant

 Author: A. Tsitovich
         CM Wintersteiger
         
\*******************************************************************/

#include "equalities.h"

/*******************************************************************\
 
 Function: equalities_invariant_testt::get_invariants

 Inputs:

 Outputs:

 Purpose: Tests for possible equalities

 \*******************************************************************/

void equalities_invariant_testt::get_invariants(
  const loop_summaryt &summary,
  std::set<exprt> &potential_invariants)
{
  set_operator("=");
  variable_relations_invariant_testt::get_invariants(summary, 
                                                     potential_invariants);
}
