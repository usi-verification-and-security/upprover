/*******************************************************************\
 
 Module: An disequalities domain invariant

 Author: A. Tsitovich
         CM Wintersteiger
         
\*******************************************************************/

#include <ansi-c/expr2c.h>

#include "disequalities.h"

/*******************************************************************\
 
 Function: disequalities_invariant_testt::get_invariants

 Inputs:

 Outputs:

 Purpose: Tests for possible disequalities

 \*******************************************************************/

void disequalities_invariant_testt::get_invariants(
  const loop_summaryt &summary,
  std::set<exprt> &potential_invariants)
{
  set_operator("!=");
  variable_relations_invariant_testt::get_invariants(summary, 
                                                     potential_invariants);
}
