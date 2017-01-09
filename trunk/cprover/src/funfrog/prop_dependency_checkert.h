/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

/* 
 * File:   prop_dependency_checkert.h
 * Author: karinek
 *
 * Created on 09 January 2017, 15:13
 */

#ifndef PROP_DEPENDENCY_CHECKERT_H
#define PROP_DEPENDENCY_CHECKERT_H

#include "dependency_checker.h"
#include "partitioning_target_equation.h"
#include "prop_partitioning_target_equation.h"
#include <solvers/flattening/bv_pointers.h>

class prop_dependency_checkert :public dependency_checkert 
{
public:
    prop_dependency_checkert(
          const namespacet &_ns,
          ui_message_handlert &_message_handler,
          const goto_programt &_goto_program,
          subst_scenariot &_omega,
          int fraction) : dependency_checkert(_ns,
          _message_handler, _goto_program, _omega,fraction) {}
    virtual ~prop_dependency_checkert() {}
    
    virtual pair<bool, fine_timet> check_implication(SSA_step_reft &c1, SSA_step_reft &c2);
    virtual long find_implications();
private:
  void deep_convert_guards(prop_conv_solvert &prop_conv, exprt exp);
  void set_guards_to_true(prop_conv_solvert &prop_conv, exprt exp);

  void convert_delta_SSA(prop_conv_solvert &prop_conv, SSA_step_reft &it1, SSA_step_reft &it2);
  void convert_assignments(prop_conv_solvert &prop_conv, SSA_step_reft &it1, SSA_step_reft &it2);
  void convert_assumptions(prop_conv_solvert &prop_conv, SSA_step_reft &it1, SSA_step_reft &it2);
  void convert_assertions(prop_conv_solvert &prop_conv, SSA_step_reft &it2);
  void convert_guards(prop_conv_solvert &prop_conv, SSA_step_reft &it1, SSA_step_reft &it2);
  void convert_io(prop_conv_solvert &prop_conv, SSA_step_reft &it1, SSA_step_reft &it2);
};

#endif /* PROP_DEPENDENCY_CHECKERT_H */

