/*******************************************************************\

Module: Model Checker Base Class

Author: Daniel Kroening
        Karen Yorav 

Date: June 2003

\*******************************************************************/

#ifndef CPROVER_CEGAR_MODELCHECKER_H
#define CPROVER_CEGAR_MODELCHECKER_H

#include "../loop_component.h"
#include "abstract_counterexample.h"

/* A general purpose model checker */
class modelcheckert:public loop_componentt
{
public:
  modelcheckert(const loop_componentt::argst &args):
    loop_componentt(args)
    {
    }

  // A return value of TRUE means the program is correct,
  // if FALSE is returned, counterexample will contain the counterexample
  virtual bool check(
    abstract_modelt &abstract_model,
    abstract_counterexamplet &abstract_counterexample)=0;

  virtual void enable_loop_detection();
  
  virtual std::string description() const=0;

  // save the model into a file
  virtual void save(
    abstract_modelt &abstract_model,
    unsigned sequence)=0;

protected:
  // auxiliary functions

  std::vector<std::string> variable_names;
  
  static bool is_variable_name(const std::string &variable_name);
  void get_variable_names(const abstract_modelt &abstract_model);  

  typedef std::map<exprt, std::string> nondet_symbolst;
  nondet_symbolst nondet_symbols;
  
  void get_nondet_symbols(const abstract_modelt &abstract_model);
  void get_nondet_symbols(const exprt &expr);
  
  class inlinedt
  {
  public:
    inlinedt(message_handlert &_mh) : message(_mh) {}

    struct instructiont
    {
      abstract_programt::targett original;
      typedef std::vector<unsigned> targetst;
      targetst targets;
    };
    
    typedef std::vector<instructiont> PC_mapt;
    PC_mapt PC_map;

    void build(abstract_modelt &abstract_model);
    
    bool has_assertion() const;
    
  protected:
    messaget message;

    void build(abstract_modelt &abstract_model,
               const irep_idt f_id,
               std::set<irep_idt> &recursion_stack);
  };
};

#endif
