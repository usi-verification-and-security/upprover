/*******************************************************************\
  
Module: Predicate Refinement for CEGAR

Author: Daniel Kroening

Date: June 2003
 
\*******************************************************************/

#include "refiner.h"
#include "../abstractor/discover_predicates.h"

/*******************************************************************\

Function: refinert::add_predicates

  Inputs:

 Outputs:

 Purpose: generate a new set of predicates given an expressions

\*******************************************************************/

void refinert::add_predicates(
  abstract_programt::targett pc,
  predicatest &predicates,
  const exprt &expr,
  bool &found_new,
  wheret where)
{
  std::set<predicatet> new_predicates;
  discover_predicates(expr, new_predicates, concrete_model.ns);
  
  std::set<unsigned> new_predicates_no;

  // we just take them all
  for(std::set<predicatet>::const_iterator
      p_it=new_predicates.begin();
      p_it!=new_predicates.end();
      p_it++)
  {
    const exprt &p=*p_it;

    if(!predicates.find(p))
    {
      std::string msg="Adding predicate `"+from_expr(concrete_model.ns, "", p)+"'";
      debug(msg);
      debug(p.pretty());
    }

    new_predicates_no.insert(predicates.lookup(*p_it));
  }
    
  std::set<unsigned> &trans_predicates=
    where==FROM?
      pc->code.transition_relation.from_predicates:
      pc->code.transition_relation.to_predicates;

  unsigned old=trans_predicates.size();

  for(std::set<unsigned>::const_iterator
      p_it=new_predicates_no.begin();
      p_it!=new_predicates_no.end();
      p_it++)
    trans_predicates.insert(*p_it);

  if(trans_predicates.size()>old)
  {
    found_new=true;
    pc->code.re_abstract=true;
  }
}

