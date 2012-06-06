/*******************************************************************\

Module: Refiner

Author: Daniel Kroening
        Karen Yorav 

Date: June 2003

Purpose: Calculate predicates for predicate abstraction.

\*******************************************************************/

#ifndef CPROVER_SATABS_REFINER_WP_H
#define CPROVER_SATABS_REFINER_WP_H

#include <map>
#include <set>
#include "transition_refiner.h"

class refiner_wpt:public transition_refinert
{
public:
  refiner_wpt(const argst &args, bool _prefix_first):
    transition_refinert(args, _prefix_first)
  {
  }

protected:
  // Updates the set of predicates for the same program according to
  // the counterexample. 
  virtual bool refine_prefix(
    predicatest &predicates, 
    abstract_modelt &abstract_model,
    const fail_infot &fail_info);

  // adds initialization instructions for predicates
  // that use freshly introduced induction variables
  virtual void add_induction_predicates(
    const fail_infot &fail_info,
    abstract_modelt &abstract_model,
    predicatest &predicates);

  virtual void add_induction_transitions(
    const fail_infot &fail_info,
    abstract_modelt &abstract_model,
    predicatest &predicates);

  virtual void add_induction_instruction(
    const abstract_programt::targett target,
    exprt &concrete_instruction,
    abstract_modelt &abstract_model,
    predicatest &predicates);

  static void push_induction_info(
    const fail_infot &fail_info,
    abstract_counterexamplet::stepst::const_iterator c_it,
    std::list<fail_infot::induction_infot> &info_stack);

  static bool get_recurrence(
    const goto_programt::const_targett &concrete_pc,
    const std::list<fail_infot::induction_infot> &info_stack,
    exprt &predicate);

  static bool get_instruction(
    const goto_programt::const_targett &concrete_pc,
    const std::list<fail_infot::induction_infot> &info_stack,
    codet &instruction,
    exprt &invariant);

private:
  // used to store from and to predicates for instructions
  // that are added by add_induction_instruction
  std::map<abstract_programt::targett, std::set<exprt> > from_predicates;
  std::map<abstract_programt::targett, std::set<exprt> > to_predicates;

  void initialize_from_to_predicates(
    const abstract_programt::targett head,
    const abstract_programt::targett exit);
};

#endif
