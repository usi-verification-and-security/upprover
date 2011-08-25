/*******************************************************************\

Module: Abstractor (generates abstract program given a set of predicates)

Author: Daniel Kroening
        Karen Yorav 

Date: June 2003

\*******************************************************************/

#ifndef CPROVER_CEGAR_ABSTRACTOR_WP_H
#define CPROVER_CEGAR_ABSTRACTOR_WP_H

#include "abstractor.h"

class abstractor_wpt:public abstractort
{
public:
  abstractor_wpt(const argst &args): abstractort(args)
  {
  }
  
protected:
  virtual void pred_abstract_block(
    goto_programt::const_targett target,
    const predicatest &predicates,
    abstract_transition_relationt &
    abstract_transition_relation);
};

#endif
