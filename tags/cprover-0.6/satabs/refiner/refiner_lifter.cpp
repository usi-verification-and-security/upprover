/*******************************************************************\
  
Module: Predicate Refinement for CEGAR

Author: Daniel Kroening

Date: September 2005
 
\*******************************************************************/

#include <assert.h>
#include <iostream>

#include "refiner_lifter.h"
#include "../abstractor/discover_predicates.h"
#include "../abstractor/canonicalize.h"

//#define DEBUG

/*******************************************************************\

Function: refiner_liftert::refine_prefix

  Inputs:

 Outputs:

 Purpose: generate a new set of predicates given a spurious counterexample

\*******************************************************************/

bool refiner_liftert::refine_prefix(
  predicatest &predicates, 
  abstract_modelt &abstract_model,
  const fail_infot &fail_info)
{
  status("Refining set of predicates according to counterexample");

  return true;
}
