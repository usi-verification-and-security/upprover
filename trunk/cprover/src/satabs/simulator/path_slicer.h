/*******************************************************************\

Module: Path Slicer

Author: Daniel Kroening
    
Date: September 2006

Purpose:

\*******************************************************************/

#ifndef CPROVER_SATABS_PATH_SLICER_H
#define CPROVER_SATABS_PATH_SLICER_H

#include <namespace.h>

#include "../modelchecker/abstract_counterexample.h"

void path_slicer(
  const namespacet &ns,
  const abstract_functionst &abstract_functions,
  abstract_counterexamplet &abstract_counterexample);

#endif
