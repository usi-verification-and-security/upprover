/*******************************************************************\

Module: Storage class for function summaries (union-find).

Author: Ondrej Sery

\*******************************************************************/

#ifndef CPROVER_SUMMARY_STORE_H
#define CPROVER_SUMMARY_STORE_H

#include <ostream>
#include <unordered_set>
#include <unordered_map>
#include <map>
#include "solvers/itp.h"

#include "summary_store_fwd.h"

class smtcheck_opensmt2t;
class call_tree_nodet;

/*KE: Abstract class, has implementation as either prop_summary_storet or smt_summary_storet */
class summary_storet
{
public:
  summary_storet() : max_id (0), repr_count(0) {}
 virtual ~summary_storet() { store.clear(); } // Virtual for sub-class

  // Serialization
  virtual void serialize(std::ostream& out) const=0;
  virtual void deserialize(std::vector<std::string> fileNames) = 0;

  
  // An already stored summary is implied by the new one - it is released
  // and represented by the stronger one, the id is still valid but represented
  // by the new one.
  void replace_summary(summary_idt old_summary_id, summary_idt replacement_id);
  // Inserts a new summary, the given summary is invalidated
  virtual void insert_summary(summaryt *summary, const irep_idt &function_name) = 0;
  // Finds the representative of the given summary
  summaryt& find_summary(summary_idt new_id) const;
  unsigned n_of_summaries() { return store.size(); }
  std::size_t get_next_id(const string &fname);
  
  // Reset the summary store
  void clear() { store.clear(); max_id = 0; repr_count = 0; function_to_summaries.clear();}


  bool has_summaries(irep_idt function_id) const {
      return function_to_summaries.find(function_id) != function_to_summaries.end();
  }

  const summary_idst& get_summaries(irep_idt function_id) const{
      return function_to_summaries.at(function_id);
  }
protected:

  // Union find node
  struct nodet {
    
    nodet(summary_idt _repr_id) : summary{nullptr}, repr_id{_repr_id}  { }

    nodet(summary_idt _repr_id, summaryt * summary) : summary{summary}, repr_id{_repr_id}  { }

    nodet() : summary(nullptr), repr_id(0) {}
    
    ~nodet() = default;

    nodet(const nodet& other) = delete;

    nodet& operator=(const nodet& other) = delete;

    nodet(nodet&& other) = default;
    nodet& operator=(nodet&& other) = default;
    
    bool is_repr() const { return summary != nullptr; }
    
    void update_repr(summary_idt _repr_id) {
      if (is_repr()) {
        summary.reset(nullptr);
      }
      repr_id = _repr_id;
    }
    
    // The summary itself
    std::unique_ptr<summaryt> summary;
    // Keeps id of the representative (if the node is representative, than this
    // means its own id)
    summary_idt repr_id;
  };
  
  std::map<std::string, std::size_t> next_ids;

  const nodet& find_repr(summary_idt id) const;
  
  // Maximal used id
  summary_idt max_id;
  summary_idt repr_count;
          
  typedef std::vector<nodet> storet;
  storet store;

  std::unordered_map<irep_idt, summary_idst, irep_id_hash> function_to_summaries;
};

#endif
