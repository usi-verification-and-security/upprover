/*******************************************************************
 Module: An inequalities domain invariant

 Author: A. Tsitovich
 
 \*******************************************************************/

#ifndef __CPROVER_LOOPFROG_INVARIANTS_INEQUALITIES_H_
#define __CPROVER_LOOPFROG_INVARIANTS_INEQUALITIES_H_

#include "variable_relations_base.h"

class inequalities_invariant_testt : public variable_relations_invariant_testt
{
public:
  inequalities_invariant_testt(contextt &context) :
    variable_relations_invariant_testt("INEQ", "Inequalities Domain", context) {};
    
  virtual ~inequalities_invariant_testt() {};

  virtual void get_invariants(
    const loop_summaryt &summary,
    std::set<exprt> &potential_invariants);
};

#endif /*__CPROVER_LOOPFROG_INVARIANTS_INEQUALITIES_H_*/
