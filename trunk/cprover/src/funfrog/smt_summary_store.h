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
   explicit smt_summary_storet(smtcheck_opensmt2t * _decider):
           summary_storet(),
           decider(_decider)
   {}

  smt_summary_storet() : smt_summary_storet(nullptr) {}

  virtual void serialize(std::ostream& out) const override;
  virtual void deserialize(std::vector<std::string> fileNames) override;
  summary_idt insert_summary(itpt_summaryt *summary_given, const std::string & function_name) override;

  void set_decider(smtcheck_opensmt2t * _decider) {
      this->decider = _decider;
  }
  summary_idt insert_conjoin_summaries(const std::string &function_name);

private:
    smtcheck_opensmt2t * decider;
};

#endif
