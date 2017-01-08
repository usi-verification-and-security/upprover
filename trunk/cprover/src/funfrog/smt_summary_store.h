/*******************************************************************\

Module: Storage class for function summaries (union-find).

Author: Ondrej Sery

\*******************************************************************/

#ifndef CPROVER_SMT_SUMMARY_STORE_H
#define CPROVER_SMT_SUMMARY_STORE_H

#include "summary_store.h"

/* Created two classes to separate the creation of SMT summaries and Propositional encoding summaries */
class smt_summary_storet :public summary_storet 
{
public:
  virtual void serialize(std::ostream& out) const;
  virtual void deserialize(const std::string& in, smtcheck_opensmt2t *decider = NULL);

protected:
  virtual void deserialize(std::istream& in) {assert(0);} // must have the interface to opensmt2
};

#endif
