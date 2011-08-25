/*******************************************************************\

Module: Predicate Manager

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <langapi/language_util.h>

#include "predicates.h"

/*******************************************************************\

Function: predicatest::lookup

  Inputs:

 Outputs:

 Purpose: find (and add, if not found) a predicate

\*******************************************************************/

unsigned predicatest::lookup(const predicatet &predicate)
{
  std::pair<predicate_mapt::iterator, bool> result=
    predicate_map.insert(
    std::pair<predicatet, unsigned>
    (predicate, predicate_vector.size()));

  if(result.second) // already there?
  {
    // actually inserted
    predicate_vector.push_back(result.first);
  }

  return result.first->second;
}

/*******************************************************************\

Function: operator<<

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::ostream& operator<< (std::ostream& out,
                          const predicatest &predicates)
{
  for(unsigned i=0; i<predicates.size(); i++)
  {
    contextt context;
    namespacet ns(context);
    out << "b" << i << " <=> "
        << from_expr(ns, "", predicates[i]) << std::endl;
  }

  return out;
}

/*******************************************************************\

Function: operator==

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool operator== (const predicatest &p1, const predicatest &p2)
{
  return p1.predicate_vector==p2.predicate_vector;
}
