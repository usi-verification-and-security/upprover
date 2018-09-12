/*******************************************************************\

Module: Storage class for function summaries (union-find).

Author: Ondrej Sery

\*******************************************************************/

#ifndef SMT_Z3_SUMMARY_STORE_H
#define SMT_Z3_SUMMARY_STORE_H

#include "summary_store.h"

class smtcheck_z3t;

/* Created two classes to separate the creation of SMT summaries in Z3 and Propositional encoding summaries */
class smt_z3_summary_storet :public summary_storet 
{
public:
   explicit smt_z3_summary_storet(smtcheck_z3t * _decider):
           summary_storet{},
           m_decider(_decider)
   {}

  smt_z3_summary_storet() : smt_z3_summary_storet(nullptr) {}

  virtual void serialize(std::ostream& out) const override;
  virtual void deserialize(std::vector<std::string> fileNames) override;
  virtual void insert_summary(summaryt *summary, const std::string & function_name) override;
  
#ifdef LATTICE_REF_ALGORITHM  
  // Only CUF Solver! - TODO: remove it from interface
  virtual void refresh_summaries_tterms(std::vector<std::string> fileNames, smtcheck_opensmt2t *_decider = nullptr) override;
#endif

  void set_decider(smtcheck_z3t * decider) {
      this->m_decider = decider;
  }

private:
    smtcheck_z3t * m_decider;
    
    std::vector<std::string> get_functions(std::string);
};

#endif
