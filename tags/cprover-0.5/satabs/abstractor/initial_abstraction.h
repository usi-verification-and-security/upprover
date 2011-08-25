/*******************************************************************\

Module: Initial Abstraction

Author: Daniel Kroening
        Karen Yorav 

Date: June 2003

Purpose: Calculate predicates for predicate abstraction.

\*******************************************************************/

#ifndef CPROVER_SATABS_INITIAL_ABSTRACTION_H
#define CPROVER_SATABS_INITIAL_ABSTRACTION_H

#include <message.h>
#include <context.h>

#include "../prepare/concrete_model.h"
#include "predicates.h"
#include "abstract_model.h"

class initial_abstractiont:public messaget
{
public:
  initial_abstractiont(message_handlert &_message_handler):
    messaget(_message_handler)
  {
  }

  // Calculates the initial set of predicates for the given
  // concrete model
  void init_preds(
    const namespacet &ns,
    predicatest &predicates, 
    const concrete_modelt &concrete_model);

  // Calculates the initial set of predicates, if they
  // are given by the user
  void init_preds(
    const namespacet &ns,
    predicatest &predicates, 
    const std::vector<exprt> &initial_predicates,
    abstract_modelt &abstract_model);

  void build(
    const concrete_modelt &concrete_model,
    abstract_modelt &abstract_model)
  {
    build_control_flow(
      concrete_model.goto_functions,
      abstract_model.goto_functions);
  }

protected:
  // Calculates the initial set of predicates for the given program
  void init_preds(
    const namespacet &ns,
    predicatest &predicates, 
    const goto_programt &goto_program);

  void init_preds(
    const namespacet &ns,
    predicatest &predicates, 
    const goto_functionst &goto_functions);

  // build control flow of abstract program
  void build_control_flow(
    const goto_functionst &concrete_functions,
    abstract_functionst &abstract_functions);

  void build_control_flow(
    const goto_programt &concrete_program,
    abstract_programt &abstract_program);
};

#endif
