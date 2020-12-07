/*******************************************************************\

Module: Storage class for function summaries (union-find).

\*******************************************************************/

#include "solvers/prop_itp.h"
#include "prop_summary_store.h"

#include <fstream>
#include <iostream>

// Serialization Prop-logic
void prop_summary_storet::serialize(std::ostream& out) const
{
  out << max_id << std::endl;

    // serializing the summaries
  for (const auto & summary_node : store) {

    out << summary_node.id << " " << true << std::endl;
    
    summary_node.summary->serialize(out);
  }

  // serializing mapping of function names to summary ids
  out << '\n';
  out << this->fname_to_summaryIDs.size() << '\n';
  for (const auto & summaries_for_function : this->fname_to_summaryIDs) {
      out << summaries_for_function.first << ' ';
      out << summaries_for_function.second.size() << '\n';
      for (auto summary_id : summaries_for_function.second) {
          out << summary_id << ' ';
      }
      out << '\n';
  }
}

// Prop-logic deser
void prop_summary_storet::deserialize(std::istream& in)
{
  this->clear();
  in >> max_id;

  if (in.fail())
    return;

  store.reserve(max_id);

  // deserializing the summaries
  for (unsigned i = 0; i < max_id; ++i)
  {
    summary_idt repr_id;
    bool is_repr;
    prop_summaryt * summary = new prop_summaryt{};
    
    in >> repr_id >> is_repr;
    
    assert(is_repr);
    if (is_repr) {
      summary->deserialize(in);     //reads raw data(in prop just numbers) one by one
      store.emplace_back(repr_id, summary);   //2-args C'tor of nodet gets called
      repr_count++;
    }
  }

  // deserializing the map from function name to summary ids
  unsigned int function_count;
  in >> function_count;
  for(unsigned int i = 0; i < function_count; ++i) {
      std::string name;
      in >> name;
      unsigned int summary_count;
      in >> summary_count;
      auto & ids = fname_to_summaryIDs[name];
      for (unsigned int j = 0; j < summary_count; ++j) {
            unsigned int id;
            in >> id;
            ids.push_back(id);
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

    this->deserialize(in);    //reads all the content of the __summary file and fills up corresponding data structures

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