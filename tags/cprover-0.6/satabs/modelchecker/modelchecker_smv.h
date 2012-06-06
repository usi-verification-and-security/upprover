/*******************************************************************\

Module: SMV Model Checker Interface

Author: Daniel Kroening

  Date: June 2003

\*******************************************************************/

#ifndef CPROVER_CEGAR_MODELCHECKER_SMV_H
#define CPROVER_CEGAR_MODELCHECKER_SMV_H

#include <iostream>

#include "modelchecker.h"

class modelchecker_smvt:public modelcheckert
{
public:
  typedef enum { CMU_SMV, NUSMV, SATMC, CADENCE_SMV } enginet;
 
  modelchecker_smvt(
    const loop_componentt::argst &args,
    enginet _engine):
    modelcheckert(args),
    engine(_engine),
    inlined(args.message_handler)
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
    case CMU_SMV:     return "CMU SMV";
    case NUSMV:       return "NuSMV";
    case SATMC:       return "SATMC";
    case CADENCE_SMV: return "Cadence SMV";
    default:;
    }
    
    assert(false);
    return "";
  }
  
  virtual void save(
    abstract_modelt &abstract_model,
    unsigned sequence);

private:
  class threadt
  {
  public:
    unsigned initial_PC;
  };
  
  typedef std::list<threadt> threadst;
  void build_threads(threadst &dest);

  enginet engine;
 
  void build_smv_file(
    const abstract_modelt &abstract_model,
    const threadst &threads,
    std::ostream &out);

  void build_smv_file(
    const abstract_modelt &abstract_model,
    std::ostream &out);

  void build_smv_file_local_variables(
    const abstract_modelt &abstract_model,
    std::ostream &out);

  void build_smv_file_guards(
    const abstract_modelt &abstract_model,
    std::ostream &out);

  void build_smv_file_control(
    const abstract_modelt &abstract_model,
    std::ostream &out);

  void build_smv_file_global_variables(
    const abstract_modelt &abstract_model,
    std::ostream &out);

  void build_smv_file_model(
    const abstract_modelt &abstract_model,
    std::ostream &out);

  void build_smv_file_spec(
    const abstract_modelt &abstract_model,
    std::ostream &out);
    
  void build_smv_file_sync(
    const abstract_modelt &abstract_model,
    std::ostream &out);

  void build_targets(unsigned PC, std::ostream &out);
    
  bool read_result(
    std::istream &out1,
    std::istream &out2,
    std::istream &out_ce,
    abstract_modelt &abstract_model,
    const threadst &threads,
    abstract_counterexamplet &counterexample);

  bool read_result_cadence_smv(
    std::istream &out_ce,
    abstract_modelt &abstract_model,
    const threadst &threads,
    abstract_counterexamplet &counterexample);

  void read_counterexample(
    const std::list<std::string> &file,
    std::list<std::string>::const_iterator it,
    abstract_modelt &abstract_model,
    const threadst &threads,
    abstract_counterexamplet &counterexample);

  void read_counterexample_cadence_smv(
    const std::list<std::string> &file,
    std::list<std::string>::const_iterator it,
    abstract_modelt &abstract_model,
    const threadst &threads,
    abstract_counterexamplet &counterexample);

  class smv_ce_thread_infot
  {
  public:
    std::vector<bool> guards;
    const threadt *t;
    unsigned PC;
    bool runs;

    void build(
      const inlinedt &inlined,
      const threadt &thread);
  };

  typedef std::vector<smv_ce_thread_infot> thread_infost;
    
  void read_counterexample_store(
    const abstract_modelt &abstract_model,
    abstract_counterexamplet &counterexample,
    thread_infost &thread_infos,
    abstract_stept &abstract_state);
    
  void instantiate_expression(exprt &expr);
  std::string instantiate(const exprt &expr);
  exprt convert_schoose_expression(const exprt &expr, const exprt &guard);
  bool threaded;
  
  // we need the program inlined
  inlinedt inlined;
};

#endif
