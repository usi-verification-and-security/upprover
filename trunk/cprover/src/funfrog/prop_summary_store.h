/*******************************************************************\

Module: Storage class for function summaries (union-find).

Author: Ondrej Sery

\*******************************************************************/

#ifndef CPROVER_PROP_SUMMARY_STORE_H
#define CPROVER_PROP_SUMMARY_STORE_H

#include "summary_store.h"

/* Created two classes to separate the creation of SMT summaries and Propositional encoding summaries */
class prop_summary_storet :public summary_storet 
{
public:
  virtual void serialize(std::ostream& out) const;
  virtual void deserialize(const std::string& in, smtcheck_opensmt2t *decider = NULL);

protected:
  virtual void deserialize(std::istream& in);
};

#endif
