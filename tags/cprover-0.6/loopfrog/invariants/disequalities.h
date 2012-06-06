/*******************************************************************
 Module: An equalities/inequalities/disequalities domain invariant

 Author: A. Tsitovich
 
 \*******************************************************************/

#ifndef __CPROVER_LOOPFROG_INVARIANTS_DISEQUALITIES_H_
#define __CPROVER_LOOPFROG_INVARIANTS_DISEQUALITIES_H_

#include "variable_relations_base.h"

class disequalities_invariant_testt : public variable_relations_invariant_testt
{
public:
  disequalities_invariant_testt(contextt &context) :
    variable_relations_invariant_testt("DQ", "Disequalities Domain", context) {};
    
  virtual ~disequalities_invariant_testt() {};

  virtual void get_invariants(
    const loop_summaryt &summary,
    std::set<exprt> &potential_invariants);
};

#endif /*__CPROVER_LOOPFROG_INVARIANTS_DISEQUALITIES_H_*/
