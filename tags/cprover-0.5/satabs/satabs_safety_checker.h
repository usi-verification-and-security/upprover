/*******************************************************************\

Module: Safety Checker Interface

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_SATABS_SAFETY_CHECKER_H
#define CPROVER_SATABS_SAFETY_CHECKER_H

#include <time_stopping.h>

#include <goto-programs/safety_checker.h>

#include <langapi/language_ui.h>

#include "modelchecker/modelchecker.h"
#include "simulator/simulator.h"
#include "abstractor/abstractor.h"
#include "refiner/refiner.h"

class satabs_safety_checkert:public safety_checkert
{
public:
  explicit satabs_safety_checkert(
    const namespacet &_ns,
    abstractort &abstractor,
    refinert &refiner,
    modelcheckert &modelchecker,
    simulatort &simulator);

  // you can add some predicates that are there right
  // from the beginning
  std::vector<exprt> initial_predicates;

  // ui
  language_uit::uit ui;

  // how many times to go through CEGAR
  unsigned max_iterations;

  // save the Boolean programs?
  bool save_bps;

  virtual resultt operator()(
    const goto_functionst &goto_functions);

  void re_abstract(const goto_programt::const_targett target);

protected:
  // the four well-known components of the CEGAR loop
  abstractort &abstractor;
  refinert &refiner;
  modelcheckert &modelchecker;
  simulatort &simulator;

  // collecting statistics

  fine_timet total_time;
  fine_timet abstractor_time;
  fine_timet modelchecker_time;
  fine_timet simulator_time;
  fine_timet refiner_time;

  void show_statistics();
  
  // implementation
  
  unsigned iteration;
  predicatest predicates;

  void do_abstraction();

  void do_refinement(
    const abstract_counterexamplet &abstract_counterexample,
    class fail_infot &fail_info);

  bool do_modelchecking(
    const concrete_modelt &concrete_model,
    abstract_counterexamplet &abstract_counterexample);

  bool do_simulation(
    abstract_counterexamplet &abstract_counterexample,
    concrete_counterexamplet &concrete_counterexample,
    fail_infot &fail_info);
};

#endif
