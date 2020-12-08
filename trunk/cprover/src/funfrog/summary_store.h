/*******************************************************************\

Module: Storage class for function summaries (union-find).

Initiated by Ondrej Sery

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
#ifdef PRINT_DEBUG_UPPROVER
#include <iostream>
#endif
/*KE: Abstract class, has implementation as either prop_summary_storet or smt_summary_storet */
class summary_storet
{
public:
  summary_storet() : max_id (1), repr_count(0) {} //summary IDs start from 1; reserve 0 for no-summary
  virtual ~summary_storet() { store.clear(); } // Virtual for sub-class
 
  virtual void serialize(std::ostream& out) const=0;
  virtual void deserialize(std::vector<std::string> fileNames) = 0;
    
  //store summaries into a given file
  void serialize(std::string file_name);
    
  // Inserts a new summary, the given summary is invalidated
  virtual summary_idt insert_summary(itpt_summaryt *summary_given, const std::string & fname_countered);
  
  // Finds the representative of the given summary
  itpt_summaryt& find_summary(summary_idt new_id) const;
  
  unsigned n_of_summaries() { return store.size(); }
  std::size_t get_next_id(const std::string &fname);
  
  // Reset the summary store
  void clear() { store.clear(); max_id = 1; repr_count = 0; fname_to_summaryIDs.clear();}


  bool function_has_summaries(const std::string & function_name) const {
      auto it = fname_to_summaryIDs.find(function_name);
      //return if found & if the entry is not empty
      return it != fname_to_summaryIDs.end() && !it->second.empty();
  }
  
  //usage in UpProver
    bool node_has_summaries(const call_tree_nodet* node);
    
  bool id_exists (const summary_idt id) {
    std::unordered_map<summary_idt,itpt_summaryt*>::iterator it = id_to_summary.find(id);
    return it != id_to_summary.end();
  }
//SA: In hifrog one func can have many summaries, but be careful in UpProver to have one-to-one mapping
  const summary_ids_vect& get_summariesID(const std::string &function_name) const{
      return fname_to_summaryIDs.at(function_name);
  }
  
  // Removes summary from the summary store
  void remove_summary(const summary_idt id){
      //1- Delete ID and its associated summary
      id_to_summary.erase(id);
      
      //2- delete from store vector
      auto it = std::remove_if(store.begin(), store.end(), [id](nodet const & node){return node.id == id; });
      if (it != store.end()) {
          store.erase(it); //remove from vector of ids
#ifdef PRINT_DEBUG_UPPROVER
          std::cout << "\n@@Deleted ID from Vec:store and ";
#endif
      }
      //3- delete from Map fname_to_summaryIDs
      bool found = false;
      for (auto & entry : fname_to_summaryIDs) {
          auto& summs = entry.second;  //vector of ids
          auto it2 = std::remove_if(summs.begin(), summs.end(), [id](summary_idt other){return other == id; });
          if (it2 != summs.end()) {
              found = true;
              summs.erase(it2);
          }
          if (found) {
#ifdef PRINT_DEBUG_UPPROVER
              std::cout <<"Map:fnameToSumIDs: "  << id <<"\n";
#endif
              break;
          }
      }
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

  std::unordered_map<std::string, summary_ids_vect> fname_to_summaryIDs;
  std::unordered_map<summary_idt, itpt_summaryt*> id_to_summary;
  //std::unordered_map<call_tree_nodet*, summary_idt> node_to_summaryID; //no-need! sumID is attribute of call-tree-node from now on.
  
};

#endif

//for upgrade check
//  void mark_used_summaries(call_tree_nodet& summary_info, bool *used_mask);
//  void remap_used_summaries(call_tree_nodet& summary_info, summary_idt *remap);
// An already stored summary is implied by the new one - it is released
// and represented by the stronger one, the id is still valid but represented
// by the new one.
//void replace_summary(summary_idt old_summary_id, summary_idt replacement_id);
