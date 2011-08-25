/*******************************************************************\

Module: Abstractor Selection

Authors: Daniel Kroening, kroening@kroening.com
         Karen Yorav

Date: September 2005

\*******************************************************************/

#ifndef CPROVER_CEGAR_SELECT_ABSTRACTOR_H
#define CPROVER_CEGAR_SELECT_ABSTRACTOR_H

#include <cmdline.h>

#include "abstractor.h"

abstractort *select_abstractor(
  const cmdlinet &cmdline,
  const loop_componentt::argst &args);

#endif
