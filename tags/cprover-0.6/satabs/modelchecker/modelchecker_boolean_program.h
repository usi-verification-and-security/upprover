/*******************************************************************\

Module: SMV Model Checker Interface

Author: Daniel Kroening

  Date: June 2003

\*******************************************************************/

#ifndef CPROVER_CEGAR_MODELCHECKER_BOOLEAN_PROGRAM_H
#define CPROVER_CEGAR_MODELCHECKER_BOOLEAN_PROGRAM_H

#include <iostream>

#include "modelchecker.h"

class modelchecker_boolean_programt:public modelcheckert
{
public:
  typedef enum { BOPPO, MOPED, BEBOP, BOOM } enginet;
 
  modelchecker_boolean_programt(
    const loop_componentt::argst &args,
    enginet _engine,
    unsigned _max_threads):
    modelcheckert(args),
    engine(_engine),
    loop_detection(false),
    max_threads(_max_threads)
  {
  }

  // A return value of TRUE means the program is correct,
  // if FALSE is returned, counterexample will contain the counterexample
  virtual bool check(
    abstract_modelt &abstract_model,
    abstract_counterexamplet &abstract_counterexample);
    
  virtual std::string description() const
  {
    switch(engine)
    {
    case BOPPO: return "Boppo";
    case MOPED: return "Moped";
    case BEBOP: return "Bebop";
    case BOOM: return "Boom";
    default:;
    }
    
    assert(false);
    return "";
  }
  
  virtual void enable_loop_detection()
  {
    if(engine!=BOPPO)
      modelcheckert::enable_loop_detection();
    else
      loop_detection=true;
  }
  
  virtual void save(
    abstract_modelt &abstract_model,
    unsigned sequence);

  virtual void build(
    abstract_modelt &abstract_model,
    const std::string &file_name);    

protected:
  enginet engine;
  bool loop_detection;
  unsigned max_threads; // 0 = no limit

  void build_boolean_program_file(
    abstract_modelt &abstract_model,
    std::ostream &out);

  void build_boolean_program_file_local_variables(
    const abstract_modelt &abstract_model,
    std::ostream &out);

  void build_boolean_program_file_functions(
    abstract_modelt &abstract_model,
    std::ostream &out);

  void build_boolean_program_file_function(
    abstract_modelt &abstract_model,
    abstract_functionst::function_mapt::iterator f_it,
    std::ostream &out);

  void build_boolean_program_file_global_variables(
    const abstract_modelt &abstract_model,
    std::ostream &out);

  void build_boolean_program_file_model(
    const abstract_modelt &abstract_model,
    std::ostream &out);

  void build_boolean_program_file_spec(
    const abstract_modelt &abstract_model,
    std::ostream &out);
    
  bool read_result_boppo_boom(
    std::istream &out1,
    std::istream &out2,
    abstract_modelt &abstract_model,
    abstract_counterexamplet &counterexample);

  void read_counterexample_boppo_boom(
    const std::string &line,
    std::list<std::pair<std::string, std::string> > &assignments,
    std::list<std::string> &labels);

  void read_counterexample_boppo_boom(
    const std::list<std::string> &file,
    abstract_modelt &abstract_model,
    abstract_counterexamplet &counterexample);

  class ce_stept
  {
  public:
    unsigned thread_nr;
    unsigned PC;
  };

  typedef std::vector<ce_stept> ce_stepst;
    
  void instantiate_expression(exprt &expr);
    
  // this maps PCs (numbers) to program locations
  typedef std::vector<abstract_programt::targett> PC_mapt;
  PC_mapt PC_map;
  
  static std::string convert_function_name(const irep_idt &name);
};

#endif
