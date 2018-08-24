/* 
 * File:   smt_dependency_checkert.h
 * Author: karinek
 *
 * Created on 09 January 2017, 15:13
 */

#ifndef SMT_DEPENDENCY_CHECKERT_H
#define SMT_DEPENDENCY_CHECKERT_H

#include "dependency_checker.h"

class smtcheck_opensmt2t;

class smt_dependency_checkert :public dependency_checkert
{
public:
    smt_dependency_checkert(
          const namespacet &_ns,
          ui_message_handlert &_message_handler,
          const goto_programt &_goto_program,
          subst_scenariot &_omega,
          int fraction,
          unsigned int SSA_steps_size) : dependency_checkert(_ns,
          _message_handler, _goto_program, _omega,fraction,SSA_steps_size) {}
    virtual ~smt_dependency_checkert() {}
    
    virtual std::pair<bool, timet> check_implication(SSA_steps_it it1, SSA_steps_it it2) override;
    virtual long find_implications() override;
private:
  void deep_convert_guards(smtcheck_opensmt2t &decider, exprt exp);
  void set_guards_to_true(smtcheck_opensmt2t &decider, exprt exp);

  void convert_delta_SSA(smtcheck_opensmt2t &decider, SSA_steps_it &it1, SSA_steps_it &it2);
  void convert_assignments(smtcheck_opensmt2t &decider, SSA_steps_it &it1, SSA_steps_it &it2);
  void convert_assumptions(smtcheck_opensmt2t &decider, SSA_steps_it &it1, SSA_steps_it &it2);
  void convert_assertions(smtcheck_opensmt2t &decider, SSA_steps_it &it2);
  void convert_guards(smtcheck_opensmt2t &decider, SSA_steps_it &it1, SSA_steps_it &it2);
  void convert_io(smtcheck_opensmt2t &decider, SSA_steps_it &it1, SSA_steps_it &it2);
};

#endif /* SMT_DEPENDENCY_CHECKERT_H */

