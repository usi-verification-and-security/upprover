/*******************************************************************\

Module: Storage class for function summaries (union-find).

\*******************************************************************/

#ifndef PROP_SUMMARY_STORE_H
#define PROP_SUMMARY_STORE_H

#include "summary_store.h"

/* Created two classes to separate the creation of SMT summaries and Propositional encoding summaries */
class prop_summary_storet :public summary_storet 
{
public:
  virtual void serialize(std::ostream& out) const override;
  virtual void deserialize(std::vector<std::string> fileNames) override;

protected:
  virtual void deserialize(std::istream& in);
  virtual void deserialize(const std::string& fileName);

};

#endif
