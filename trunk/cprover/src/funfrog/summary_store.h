/*******************************************************************\

Module: Storage class for function summaries (union-find).

Author: Ondrej Sery

\*******************************************************************/

#ifndef CPROVER_SUMMARY_STORE_H
#define CPROVER_SUMMARY_STORE_H


#include "solvers/itp.h"

#include "summary_store_fwd.h"
#include <iosfwd>
#include <unordered_set>
#include <unordered_map>
#include <map>
#include <memory>
#include <fstream>
#include <algorithm>
class call_tree_nodet;

/*KE: Abstract class, has implementation as either prop_summary_storet or smt_summary_storet */
class summary_storet
{
public:
  summary_storet() : max_id (0), repr_count(0) {}
  virtual ~summary_storet() { store.clear(); } // Virtual for sub-class
 
  virtual void serialize(std::ostream& out) const=0;
  virtual void deserialize(std::vector<std::string> fileNames) = 0;
    
  //store summaries into a given file
  void serialize(std::string file_name);
    
  // Inserts a new summary, the given summary is invalidated
  virtual summary_idt insert_summary(itpt_summaryt *summary_given, const std::string & function_name);
  
  // Finds the representative of the given summary
  itpt_summaryt& find_summary(summary_idt new_id) const;
  
  unsigned n_of_summaries() { return store.size(); }
  std::size_t get_next_id(const std::string &fname);
  
  // Reset the summary store
  void clear() { store.clear(); max_id = 0; repr_count = 0; function_to_summaries.clear();}


  bool has_summaries(const std::string & function_name) const {
      auto it = function_to_summaries.find(function_name);
      //return if found & if the entry is not empty
      return it != function_to_summaries.end() && !it->second.empty();
  }

  const summary_ids_vect& get_summariesID(const std::string &function_name) const{
      return function_to_summaries.at(function_name);
  }
  
  // Removes summary from the summary store
  void remove_summary(const summary_idt id){
      auto it = std::remove_if(store.begin(), store.end(), [id](nodet const & node){return node.id == id; });
      if (it != store.end()) {
          store.erase(it);
      }
      bool found = false;
      for (auto & entry : function_to_summaries) {
          auto& summs = entry.second;  //vector of ids
          auto it2 = std::remove_if(summs.begin(), summs.end(), [id](summary_idt other){return other == id; });
          if (it2 != summs.end()) {
              found = true;
              summs.erase(it2);
          }
          if (found) { break; }
      }
  }
  void decrease_max_id(){
      max_id--;
  }
  
protected:

  // Union find node
  struct nodet {
    
//    nodet(summary_idt _repr_id) : summary{nullptr}, repr_id{_repr_id}  { }   // C'tor initializes ID without summary

    nodet(summary_idt _repr_id, itpt_summaryt * summary) : summary{summary}, id{_repr_id}  { }  //C'tor initializes ID with Summary

    nodet() = delete;
    
    ~nodet() = default;

    nodet(const nodet& other) = delete;

    nodet& operator=(const nodet& other) = delete;

    nodet(nodet&& other) = default;
    nodet& operator=(nodet&& other) = default;
    
    // The summary itself
    std::unique_ptr<itpt_summaryt> summary;
    // Keeps id of the representative (every id is (should be) representative!)
    summary_idt id;
  };
  
  std::map<std::string, std::size_t> next_ids;

  const nodet& find_repr(summary_idt id) const;

  // Maximal used id
  summary_idt max_id;
  summary_idt repr_count;
          
  using storet = std::vector<nodet>;
  storet store;

  std::unordered_map<std::string, summary_ids_vect> function_to_summaries;
};

#endif

//for upgrade check
//  void mark_used_summaries(call_tree_nodet& summary_info, bool *used_mask);
//  void remap_used_summaries(call_tree_nodet& summary_info, summary_idt *remap);
// An already stored summary is implied by the new one - it is released
// and represented by the stronger one, the id is still valid but represented
// by the new one.
//void replace_summary(summary_idt old_summary_id, summary_idt replacement_id);
