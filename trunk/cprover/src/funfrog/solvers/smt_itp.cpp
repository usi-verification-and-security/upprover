/*******************************************************************\

Module: SMT interpolant.  Based on code on prop_itp.

Author: 

\*******************************************************************/

#include "smt_itp.h"
#include <iostream>
#include "smtcheck_opensmt2.h"

/*******************************************************************\

Function: smt_itpt::serialize

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void smt_itpt::serialize(std::ostream& out) const
{
  assert(m_decider);
  m_decider->dump_function(out, templ);
}

bool smt_itpt::equals(itpt * other) const {
    smt_itpt* smt_other = dynamic_cast<smt_itpt*>(other);
    if(!smt_other){return false;}
    return this->getInterpolant() == smt_other->getInterpolant();
}

void smt_itpt::setDecider(check_opensmt2t * _s) {
    m_decider = dynamic_cast<smtcheck_opensmt2t *> (_s);
    assert(m_decider);
}
