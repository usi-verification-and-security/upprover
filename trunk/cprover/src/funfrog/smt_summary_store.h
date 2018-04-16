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
   smt_summary_storet(smtcheck_opensmt2t * decider):
           summary_storet{},
           decider{decider}
   {}

  smt_summary_storet() : smt_summary_storet(nullptr) {}

  virtual void serialize(std::ostream& out) const override;
  virtual void deserialize(std::vector<std::string> fileNames) override;
  virtual void insert_summary(summaryt *summary, const irep_idt &function_name) override;

protected:

private:
    smtcheck_opensmt2t * decider;
};

#endif
