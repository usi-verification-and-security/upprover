/*******************************************************************\

Module: The concrete program

Author: Daniel Kroening

Date: May 2006

\*******************************************************************/

#include "substitute_invariants.h"

/*******************************************************************\

Function: substitute_invariants_rec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

#if 0
void subsitute_invariants_rec(
  const invariant_sett::invariantst &invariants,
  exprt &dest)
{
  if((dest.id()=="and" ||
      dest.id()=="or" ||
      dest.id()=="not") &&
     dest.type().id()=="bool")
  {
    Forall_operands(it, dest)
      subsitute_invariants_rec(invariants, *it);
  }
  else
  {
    #if 0
    for(invariant_sett::invariantst::expr_sett::const_iterator
      it=invariants.expr_set().begin();
      it!=invariants.expr_set().end();
      it++)
      std::cout << "I: " << it->pretty() << std::endl;
      
    std::cout << "DEST: " << dest.pretty() << std::endl;
    #endif
  
    if(invariants.expr_set().find(dest)!=
       invariants.expr_set().end())
    {
      dest.make_true();
    }
    else
    {
      // inverted?
      exprt tmp(dest);
      tmp.make_not();

      if(invariants.expr_set().find(tmp)!=
         invariants.expr_set().end())
      {
        dest.make_false();
      }
    }    
  }
}
#endif

/*******************************************************************\

Function: substitute_invariants

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void substitute_invariants(
  const concrete_modelt &concrete_model,
  abstract_programt::targett pc,
  exprt &predicate)
{
  // see if a predicate is also an invariant
  #if 0
  const invariant_sett::invariantst &invariants=
    concrete_model.invariant_propagation.lookup(pc->code.concrete_pc).invariants;
    
  subsitute_invariants_rec(invariants, predicate);
  #endif
}
