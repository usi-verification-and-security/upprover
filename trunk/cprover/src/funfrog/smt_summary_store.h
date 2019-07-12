/*******************************************************************\

Module: Storage class for function summaries (union-find).

\*******************************************************************/

#ifndef SMT_SUMMARY_STORE_H
#define SMT_SUMMARY_STORE_H

#include "summary_store.h"

class smtcheck_opensmt2t;

/* Created two classes to separate the creation of SMT summaries and Propositional encoding summaries */
class smt_summary_storet :public summary_storet 
{
public:
   explicit smt_summary_storet(smtcheck_opensmt2t * decider):
           summary_storet{},
           decider{decider}
   {}

  smt_summary_storet() : smt_summary_storet(nullptr) {}

  virtual void serialize(std::ostream& out) const override;
  virtual void deserialize(std::vector<std::string> fileNames) override;
  virtual summary_idt insert_summary(summaryt *summary_given, const std::string & function_name) override;

  void set_decider(smtcheck_opensmt2t * decider) {
      this->decider = decider;
  }

private:
    smtcheck_opensmt2t * decider;
};

#endif
