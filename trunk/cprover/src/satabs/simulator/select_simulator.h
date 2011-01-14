/*******************************************************************\

Module: Simulator Selection

Authors: Daniel Kroening, kroening@kroening.com
         Karen Yorav

Date: June 2003

\*******************************************************************/

#ifndef CPROVER_CEGAR_SELECT_SIMULATOR_H
#define CPROVER_CEGAR_SELECT_SIMULATOR_H

#include <cmdline.h>

#include "simulator.h"

simulatort *select_simulator(
  const cmdlinet &cmdline,
  const loop_componentt::argst &args,
  contextt &_shadow_context);

#endif
