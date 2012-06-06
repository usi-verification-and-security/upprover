/*******************************************************************\

Module: Abstractor (generates abstract program given a set of predicates)

Author: Daniel Kroening
        Karen Yorav 

Date: June 2003

\*******************************************************************/

#ifndef CPROVER_CEGAR_ABSTRACTOR_H
#define CPROVER_CEGAR_ABSTRACTOR_H

#include "../loop_component.h"
#include "../abstractor/abstract_model.h"
#include "../abstractor/predicates.h"

class abstractort:public loop_componentt
{
public:
  abstractort(const argst &args):
    loop_componentt(args)
  {
  }

  ~abstractort()
  {
  }

  // Generates the abstract program given a concrete program
  // and a set of predicates.
  void build_abstraction(const predicatest &predicates);

  void abstract_variables(
    const predicatest &predicates,
    abstract_modelt::variablest &variables);

  abstract_modelt abstract_model;
  
protected:
  abstract_modelt::variablet::var_classt get_var_class(
    const predicatet &predicate);

  void build_abstraction(
    const predicatest &predicates,
    const goto_programt &goto_program,
    abstract_programt &abstract_program);

  // compute abstract transition relation from
  // equations and predicates

  virtual void pred_abstract_block(
    goto_programt::const_targett target,
    const predicatest &predicates,
    abstract_transition_relationt &
    abstract_transition_relation)=0;
    
  // remember the old predicates
  predicatest old_predicates;
  bool have_new_predicates;
  
  static exprt get_value(
    unsigned p_nr,
    const predicatest &predicates,
    const exprt &value);
};

#endif
