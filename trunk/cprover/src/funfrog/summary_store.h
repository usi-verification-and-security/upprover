/*******************************************************************\

Module: Storage class for function summaries (union-find).

Author: Ondrej Sery

\*******************************************************************/

#ifndef CPROVER_SUMMARY_STORE_H
#define CPROVER_SUMMARY_STORE_H

#include <ostream>
#include "solvers/prop_itp.h"

typedef prop_itpt summaryt;
typedef long unsigned summary_idt;
typedef std::vector<summary_idt> summary_idst;
typedef hash_set_cont<summary_idt> summary_ids_sett;
class summary_infot;
class function_infot;
typedef hash_map_cont<irep_idt, function_infot, irep_id_hash> function_infost;

class summary_storet
{
public:
  summary_storet() : max_id (0), repr_count(0) {}

  // Serialization
  void serialize(std::ostream& out) const;
  void deserialize(std::istream& in);

  // Compacts the store representation, only representatives are kept.
  void compact_store(summary_infot& summary_info, 
          function_infost& function_infos);
  
  // An already stored summary is implied by the new one - it is released
  // and represented by the stronger one, the id is still valid but represented
  // by the new one.
  void replace_summary(summary_idt old_summary_id, summary_idt replacement_id);
  // Inserts a new summary, the given summary is invalidated
  summary_idt insert_summary(summaryt& summary);
  // Finds the representative of the given summary
  summaryt& find_summary(summary_idt new_id);
  
  // Reset the summary store
  void clear() { store.clear(); max_id = 0; repr_count = 0; }

private:

  // Union find node
  struct nodet {
    // Note that the given summary is destroyed
    nodet(summary_idt id, summaryt& _summary) : repr_id(id) {
      summary = new summaryt();
      summary->swap(_summary);
    }
    
    nodet(summary_idt _repr_id) : summary(NULL), repr_id(_repr_id)  { }
    
    nodet(const nodet& other) : summary(other.summary), repr_id(other.repr_id) {
      const_cast<nodet&>(other).summary = NULL;
    }
    
    nodet() : summary(NULL), repr_id(0) {}
    
    ~nodet() { if (summary != NULL) delete summary; }
    
    bool is_repr() const { return summary != NULL; }
    
    void update_repr(summary_idt _repr_id) {
      if (is_repr()) {
        delete summary;
        summary = NULL;
      }
      repr_id = _repr_id;
    }
    
    // The summary itself
    summaryt* summary;
    // Keeps id of the representative (if the node is representative, than this
    // means its own id)
    summary_idt repr_id;
  };
  
  nodet& find_repr(summary_idt id);
  void mark_used_summaries(summary_infot& summary_info, bool used_mask[]);
  void remap_used_summaries(summary_infot& summary_info, summary_idt remap[]);
  
  // Maximal used id
  summary_idt max_id;
  summary_idt repr_count;
          
  typedef std::vector<nodet> storet;
  storet store;
};

#endif
