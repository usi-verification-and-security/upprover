/* 
 * File:   prop_dependency_checkert.h
 * Author: karinek
 *
 * Created on 09 January 2017, 15:13
 */

#ifndef PROP_DEPENDENCY_CHECKERT_H
#define PROP_DEPENDENCY_CHECKERT_H

#include "dependency_checker.h"

class prop_conv_solvert;

class prop_dependency_checkert :public dependency_checkert 
{
public:
    prop_dependency_checkert(
          const namespacet &_ns,
          ui_message_handlert &_message_handler,
          const goto_programt &_goto_program,
          subst_scenariot &_omega,
          int fraction,
          unsigned int SSA_steps_size) : dependency_checkert(_ns,
          _message_handler, _goto_program, _omega,fraction, SSA_steps_size) {}
    virtual ~prop_dependency_checkert() {}
    
    virtual std::pair<bool, fine_timet> check_implication(SSA_steps_it c1, SSA_steps_it c2) override;
    virtual long find_implications() override;
private:
  void deep_convert_guards(prop_conv_solvert &prop_conv, exprt exp);
  void set_guards_to_true(prop_conv_solvert &prop_conv, exprt exp);

  void convert_delta_SSA(prop_conv_solvert &prop_conv, SSA_steps_it &it1, SSA_steps_it &it2);
  void convert_assignments(prop_conv_solvert &prop_conv, SSA_steps_it &it1, SSA_steps_it &it2);
  void convert_assumptions(prop_conv_solvert &prop_conv, SSA_steps_it &it1, SSA_steps_it &it2);
  void convert_assertions(prop_conv_solvert &prop_conv, SSA_steps_it &it2);
  void convert_guards(prop_conv_solvert &prop_conv, SSA_steps_it &it1, SSA_steps_it &it2);
  void convert_io(prop_conv_solvert &prop_conv, SSA_steps_it &it1, SSA_steps_it &it2);
};

#endif /* PROP_DEPENDENCY_CHECKERT_H */

