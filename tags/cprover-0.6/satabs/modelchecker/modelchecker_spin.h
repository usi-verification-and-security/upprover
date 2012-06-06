/*******************************************************************\

Module: Spin Model Checker Interface

Author: Daniel Kroening

  Date: June 2003

\*******************************************************************/

#ifndef CPROVER_CEGAR_MODELCHECKER_SPIN_H
#define CPROVER_CEGAR_MODELCHECKER_SPIN_H

#include <iostream>

#include "modelchecker.h"

class modelchecker_spint:public modelcheckert
{
public:
  modelchecker_spint(const loop_componentt::argst &args):
    modelcheckert(args),
    inlined(args.message_handler)
  {
  }

  // A return value of TRUE means the program is correct,
  // if FALSE is returned, abstract_counterexample will
  // contain the counterexample
  virtual bool check(
    abstract_modelt &abstract_model,
    abstract_counterexamplet &abstract_counterexample);
    
  virtual std::string description() const
  {
    return "SPIN";
  }
  
  virtual void save(
    abstract_modelt &abstract_model,
    unsigned sequence);
    
  void build(
    abstract_modelt &abstract_model,
    const std::string &out_file_name);

private:
  void build_promela_file(
    const abstract_modelt &abstract_model,
    std::ostream &out);

  void build_promela_file_control(
    const abstract_modelt &abstract_model,
    std::ostream &out);

  void build_promela_file_global_variables(
    const abstract_modelt &abstract_model,
    std::ostream &out);

  void build_promela_file_trans(
    const abstract_modelt &abstract_model,
    const abstract_transition_relationt &abstract_transition_relation,
    std::ostream &out);

  bool read_result(
    std::istream &out1,
    std::istream &out2,
    const abstract_modelt &abstract_model,
    abstract_counterexamplet &counterexample);

  void read_counterexample(
    const std::list<std::string> &file,
    std::list<std::string>::const_iterator it,
    const abstract_modelt &abstract_model,
    abstract_counterexamplet &counterexample);

  void instantiate_expression(exprt &expr);
  
  // we need the program inlined
  inlinedt inlined;
};

#endif
