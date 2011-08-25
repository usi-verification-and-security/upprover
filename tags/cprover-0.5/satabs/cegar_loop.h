/*******************************************************************\

Module: CEGAR Loop

Author: Daniel Kroening
        Karen Yorav 

Date: June 2003

\*******************************************************************/

#ifndef CPROVER_CEGAR_CEGAR_LOOP_H
#define CPROVER_CEGAR_CEGAR_LOOP_H

#include <set>

#include <message.h>
#include <langapi/language_ui.h>
#include <time_stopping.h>
#include <expr_util.h>

#include "prepare/concrete_model.h"
#include "modelchecker/modelchecker.h"
#include "simulator/simulator.h"
#include "abstractor/abstractor.h"
#include "refiner/refiner.h"

/* This class implements the CEGAR loop, given the proper tools */

class cegar_loopt:public messaget
{
public:
  cegar_loopt(
    concrete_modelt &_concrete_model, 
    const std::vector<exprt> &_initial_predicates,
    const contextt &_context,
    const contextt &_shadow_context,
    abstractort &_abstractor,
    refinert &_refiner,
    modelcheckert &_modelchecker,
    simulatort &_simulator,
    message_handlert &_message_handler,
    language_uit::uit _ui,
    bool _show_last_trace,
    unsigned _max_iterations,
    bool _save_bps):
    messaget(_message_handler),
    concrete_model(_concrete_model),
    initial_predicates(_initial_predicates),
    context(_context),
    shadow_context(_shadow_context),
    abstractor(_abstractor),
    refiner(_refiner),
    modelchecker(_modelchecker),
    simulator(_simulator),
    ui(_ui),
    show_last_trace(_show_last_trace),
    max_iterations(_max_iterations),
    save_bps(_save_bps)
  {
  }

  int go();

  // this possibly returns a concrete counterexample if
  // the above returns 'CEGAR_COUNTEREXAMPLE'
  concrete_counterexamplet concrete_counterexample;

protected:
  void do_abstraction();

  bool do_modelchecking(
    abstract_counterexamplet &abstract_counterexample);

  bool do_simulation(
    abstract_counterexamplet &abstract_counterexample,
    concrete_counterexamplet &concrete_counterexample,
    fail_infot &fail_info);

  void do_refinement(
    const abstract_counterexamplet &abstract_counterexample,
    fail_infot &fail_info);
    
  void show_counterexample(
    const concrete_counterexamplet &concrete_counterexample);

  virtual void report_success();
  virtual void report_failure();

protected:  
  concrete_modelt &concrete_model;
  const std::vector<exprt> &initial_predicates;
  const contextt &context;
  const contextt &shadow_context;
  abstractort &abstractor;
  refinert &refiner;
  modelcheckert &modelchecker;
  simulatort &simulator;

  language_uit::uit ui;
  bool show_last_trace;
  unsigned max_iterations, iteration;
  bool save_bps;
  predicatest predicates;

  fine_timet total_time;
  fine_timet abstractor_time;
  fine_timet modelchecker_time;
  fine_timet simulator_time;
  fine_timet refiner_time;
  
  void show_statistics();
  
public:
  void re_abstract(const goto_programt::const_targett target);  
};

#endif

