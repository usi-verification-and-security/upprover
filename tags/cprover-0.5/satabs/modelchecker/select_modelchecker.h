/*******************************************************************\

Module: Model Checker Selection

Authors: Daniel Kroening, kroening@kroening.com
         Karen Yorav

Date: June 2003

\*******************************************************************/

#ifndef CPROVER_CEGAR_SELECT_MODELCHECKER_H
#define CPROVER_CEGAR_SELECT_MODELCHECKER_H

#include <cmdline.h>

#include "modelchecker.h"

modelcheckert *select_modelchecker(
  const cmdlinet &cmdline,
  const loop_componentt::argst &args);

#endif
