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

class smtcheck_opensmt2t;

typedef itpt summaryt;
typedef prop_itpt prop_summaryt;
typedef smt_itpt smt_summaryt;
typedef long unsigned summary_idt;
typedef std::vector<summary_idt> summary_idst;
typedef std::unordered_set<summary_idt> summary_ids_sett;
class summary_infot;
class function_infot;
typedef std::unordered_map<irep_idt, function_infot, irep_id_hash> function_infost;

/*KE: Abstract class, has implementation as either prop_summary_storet or smt_summary_storet */
class summary_storet
{
public:
  summary_storet() : max_id (0), repr_count(0) {}
 virtual ~summary_storet() { store.clear(); } // Virtual for sub-class

  // Serialization
  virtual void serialize(std::ostream& out) const=0;
  virtual void deserialize(const std::string& in, smtcheck_opensmt2t *decider = NULL)=0;
  virtual void refresh_summaries_tterms(const std::string& in, smtcheck_opensmt2t *decider = NULL)=0;

  // Compacts the store representation, only representatives are kept.
  void compact_store(summary_infot& summary_info, 
          function_infost& function_infos);
  
  // An already stored summary is implied by the new one - it is released
  // and represented by the stronger one, the id is still valid but represented
  // by the new one.
  void replace_summary(summary_idt old_summary_id, summary_idt replacement_id);
  // Inserts a new summary, the given summary is invalidated
  virtual summary_idt insert_summary(summaryt& summary) =0;
  // Finds the representative of the given summary
  summaryt& find_summary(summary_idt new_id);
  unsigned n_of_summaries() { return store.size(); }
  int get_max_id(const string& fname) const;
  
  // Reset the summary store
  void clear() { store.clear(); max_id = 0; repr_count = 0; }

  virtual void deserialize(std::istream& in)=0;
protected: 

  // Union find node
  struct nodet {
    // Note that the given summary is destroyed
    nodet(summary_idt id, summaryt& _summary) : repr_id(id) {
        summary = _summary.get_nodet();
        summary->swap(_summary); 
    }
    
    nodet(summary_idt _repr_id) : summary(NULL), repr_id(_repr_id)  { }
    
    nodet(const nodet& other) : summary(other.summary), repr_id(other.repr_id) {
      const_cast<nodet&>(other).summary = NULL;
    }
    
    nodet() : summary(NULL), repr_id(0) {}
    
    ~nodet() { if (summary != NULL) delete summary; }
    
    void operator=(nodet& other) {
      repr_id = other.repr_id;
      summary = other.summary;
      other.summary = NULL;
    }
    
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
  
  std::map<string, int> max_ids;

  nodet& find_repr(summary_idt id);
  void mark_used_summaries(summary_infot& summary_info, bool *used_mask);
  void remap_used_summaries(summary_infot& summary_info, summary_idt *remap);
  
  // Maximal used id
  summary_idt max_id;
  summary_idt repr_count;
          
  typedef std::vector<nodet> storet;
  storet store;
};

#endif
