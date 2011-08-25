/*******************************************************************\

Module: Counterexamples

Author: Daniel Kroening
        Karen Yorav 

Date: June 2003

\*******************************************************************/

#ifndef CPROVER_CEGAR_COUNTEREXAMPLE_H
#define CPROVER_CEGAR_COUNTEREXAMPLE_H

#include <iostream>
#include <vector>

#include <goto-programs/goto_program.h>
#include <goto-symex/goto_trace.h>

/* A concrete conterexample */

class concrete_counterexamplet
{
public:
  goto_tracet goto_trace;

  void clear()
  {
    goto_trace.clear();
  }
};

void show_counterexample(
  std::ostream &out,
  const contextt &context,
  const concrete_counterexamplet &counterexample);

void show_counterexample_gui(
  std::ostream &out,
  const contextt &context,
  const concrete_counterexamplet &counterexample);

std::ostream& operator<< (
  std::ostream& out,
  const concrete_counterexamplet &counterexample);

#endif
