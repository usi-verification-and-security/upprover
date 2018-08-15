/*******************************************************************\

Module: SMT interpolant.  Based on code on prop_itp.

Author: 

\*******************************************************************/

#include "smt_itp.h"
#include <iostream>

/*******************************************************************\

Function: smt_itpt::serialize

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt_itpt::serialize(std::ostream& out) const
{
  assert(logic);
  logic->dumpFunction(out, templ);
}

bool smt_itpt::equals(itpt * other) const {
    smt_itpt* smt_other = dynamic_cast<smt_itpt*>(other);
    if(!smt_other){return false;}
    return this->getInterpolant() == smt_other->getInterpolant();
}
