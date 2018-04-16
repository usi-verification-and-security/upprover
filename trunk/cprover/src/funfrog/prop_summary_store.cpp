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
    prop_summaryt * summary = new prop_summaryt{};
    
    in >> repr_id >> is_repr;
    
    if (is_repr) {
      in >> is_valid;
      summary->deserialize(in);
      summary->set_valid(is_valid);
      store.emplace_back(repr_id, summary);
      repr_count++;
    } else {
      store.push_back(nodet(repr_id));
    }
  }
}

// Public deser method for propositional logic
void prop_summary_storet::deserialize(const std::string& fileName)
{
    std::ifstream in;
    in.open(fileName.c_str());

    if (in.fail()) {
        std::cerr << "Failed to deserialize function summaries (file: " << fileName <<
                  " cannot be read)\n";
        return;
    }

    this->deserialize(in);

    if (in.fail()) {
        std::cerr << "Error occured during deserializing function summaries\n";
    }
    in.close();
}

void prop_summary_storet::deserialize(std::vector<std::string> fileNames) {
    if(fileNames.size() > 1) {
        throw std::logic_error {"Propositional summary store can deserialize only single file"};
    }
    if(!fileNames.empty()) {
        deserialize(fileNames[0]);
    }
}

/*******************************************************************\

Function: summary_storet::insert_summary

  Inputs:

 Outputs:

 Purpose: Inserts a new summary, the given summary is invalidated

\*******************************************************************/

void prop_summary_storet::insert_summary(summaryt *summary, const irep_idt &function_name)
{
  summary_idt id = max_id++;
  store.emplace_back(id, summary);
  repr_count++;
  function_to_summaries[function_name].push_back(id);
}