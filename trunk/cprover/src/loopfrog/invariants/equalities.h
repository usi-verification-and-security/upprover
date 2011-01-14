/*******************************************************************
 Module: An equalities domain invariant

 Author: A. Tsitovich
 
 \*******************************************************************/

#ifndef __CPROVER_LOOPFROG_INVARIANTS_EQUALITIES_H_
#define __CPROVER_LOOPFROG_INVARIANTS_EQUALITIES_H_

#include "variable_relations_base.h"

class equalities_invariant_testt : public variable_relations_invariant_testt
{
public:
  equalities_invariant_testt(contextt &context) :
    variable_relations_invariant_testt("EQ", "Equalities Domain", context){};
    
  virtual ~equalities_invariant_testt() {};

  virtual void get_invariants(
    const loop_summaryt &summary,
    std::set<exprt> &potential_invariants);
};

#endif /*__CPROVER_LOOPFROG_INVARIANTS_EQUALITIES_H_*/
