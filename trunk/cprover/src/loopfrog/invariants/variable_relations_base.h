/*******************************************************************\

Module: Relations between variables

Author: CM Wintersteiger

\*******************************************************************/

#ifndef VARIABLE_RELATIONS_BASE_H_
#define VARIABLE_RELATIONS_BASE_H_

#include "invariant_test.h"

class variable_relations_invariant_testt : public invariant_testt
{
public:
  variable_relations_invariant_testt(const std::string &shortid,
                                     const std::string &longid,
                                     contextt &context) :
    invariant_testt(shortid, longid, context){};
    
  virtual ~variable_relations_invariant_testt() {};

  virtual void get_invariants(
    const loop_summaryt &summary,
    std::set<exprt> &potential_invariants);
  
protected:
  irep_idt op;
  
  void set_operator(const irep_idt &_op) { op = _op; }
};

#endif
