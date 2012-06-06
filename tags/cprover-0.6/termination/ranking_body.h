/*******************************************************************\

Module: Ranking Body

Author: CM Wintersteiger

Date: Oct 2008

\*******************************************************************/

#ifndef CPROVER_RANKING_BODY_H_
#define CPROVER_RANKING_BODY_H_

#include <map>

class exprt;

struct bodyt
{
  exprt body_relation;

  typedef std::map<irep_idt, irep_idt> variable_mapt;

  variable_mapt variable_map; // links pre-/post-state variables
};

#endif /* CPROVER_RANKING_BODY_H_ */
