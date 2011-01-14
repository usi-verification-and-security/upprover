/*******************************************************************\

Module: Ranking Function Synthesis

Author: CM Wintersteiger

Date: September 2008

\*******************************************************************/

#ifndef CPROVER_RANKING_H
#define CPROVER_RANKING_H

#include "ranking_body.h"

exprt ranking(
  const std::string &mode,
  const bodyt &body,
  const contextt &context,
  contextt &shadow_context,
  message_handlert &mh,
  unsigned verbosity);

#endif

