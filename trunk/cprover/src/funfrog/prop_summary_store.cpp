/*******************************************************************\

Module: Storage class for function summaries (union-find).

Author: Ondrej Sery

\*******************************************************************/

#include <string.h>
#include "solvers/prop_itp.h"
#include "prop_summary_store.h"

// Serialization Prop-logic
void prop_summary_storet::serialize(std::ostream& out) const
{
  out << max_id << std::endl;

  for (storet::const_iterator it = store.begin();
          it != store.end();
          ++it) {

    out << it->repr_id << " " << it->is_repr() << std::endl;
    
    if (it->is_repr()) {
      out << it->summary->is_valid() << std::endl;
      it->summary->serialize(out);
    }
  }
}

// Prop-logic deser
void prop_summary_storet::deserialize(std::istream& in)
{
  repr_count = 0;
  in >> max_id;

  if (in.fail())
    return;

  store.clear();
  store.reserve(max_id);
  
  for (unsigned i = 0; i < max_id; ++i)
  {
    summary_idt repr_id;
    bool is_repr;
    bool is_valid;
    prop_summaryt summary;
    
    in >> repr_id >> is_repr;
    
    if (is_repr) {
      in >> is_valid;
      summary.deserialize(in);
      summary.set_valid(is_valid);
      store.push_back(nodet(repr_id, summary));
      repr_count++;
    } else {
      store.push_back(nodet(repr_id));
    }
  }
}

// Public deser method for propositional logic
void prop_summary_storet::deserialize(const std::string& in, smtcheck_opensmt2t *decider)
{
   std::istringstream in_stream(in); 
   deserialize(in_stream);
}

/*******************************************************************\

Function: summary_storet::insert_summary

  Inputs:

 Outputs:

 Purpose: Inserts a new summary, the given summary is invalidated

\*******************************************************************/

summary_idt prop_summary_storet::insert_summary(summaryt& summary)
{
  summary_idt id = max_id++;
  summary.set_valid(1);
  store.push_back(nodet(id, summary));
  repr_count++;
  return id;
}