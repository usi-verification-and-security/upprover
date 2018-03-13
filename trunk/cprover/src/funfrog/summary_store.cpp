/*******************************************************************\

Module: Storage class for function summaries (union-find).

Author: Ondrej Sery

\*******************************************************************/

#include <string.h>

#include "summary_store.h"
#include "summary_info.h"
#include "function_info.h"

summary_storet::nodet& summary_storet::find_repr(summary_idt id)
{
  nodet& node = store[id];
  
  if (node.is_repr()) {
    return node;
  }

  assert(node.repr_id != id);
  
  summary_storet::nodet& repr_node = find_repr(node.repr_id);
  node.update_repr(repr_node.repr_id);
  
  return repr_node;
}

/*******************************************************************\

Function: summary_storet::replace_summary

  Inputs:

 Outputs:

 Purpose: An already stored summary is implied by the new one - it is released
 and represented by the stronger one, the id is still valid but represented
 by the new one.

\*******************************************************************/

void summary_storet::replace_summary(summary_idt old_summary_id, 
        summary_idt replacement_id)
{
  nodet& node = store[old_summary_id];
  
  assert(old_summary_id != replacement_id);
  assert(node.is_repr());
  assert(find_repr(replacement_id).repr_id != old_summary_id);
  
  node.update_repr(replacement_id);

  repr_count--;
}

/*
 * Returns the next free id for a given function name.
 * Adjust the counter to mark the returned value as taken
 */
std::size_t summary_storet::get_next_id(const std::string &fname)
{
  // uses the fact that if the key was not in the map, it is implicitly inserted with default value -> 0
  return next_ids[fname]++;
}

/*******************************************************************\

Function: summary_storet::find_summary

  Inputs:

 Outputs:

 Purpose: Finds the representative of the given summary

\*******************************************************************/

summaryt& summary_storet::find_summary(summary_idt new_id)
{
  nodet& node = find_repr(new_id);
  
  return *(node.summary);
}


void summary_storet::mark_used_summaries(summary_infot& summary_info, 
        bool *used_mask)
{
  call_sitest& call_sites = summary_info.get_call_sites();
  
  for (call_sitest::iterator it = call_sites.begin();
          it != call_sites.end(); ++it)
  {
    const summary_ids_sett& summaries = 
      it->second.get_used_summaries();
  
    // Collect the used summaries
    if (it->second.get_precision() != HAVOC) {
      for (summary_ids_sett::const_iterator it2 = summaries.begin();
              it2 != summaries.end(); ++it2)
      {
        used_mask[find_repr(*it2).repr_id] = true;
      }
      
      // Propagate the call
      mark_used_summaries(it->second, used_mask);
    }
  }
}

void summary_storet::remap_used_summaries(summary_infot& summary_info, 
        summary_idt *remap) 
{
  call_sitest& call_sites = summary_info.get_call_sites();
  
  for (call_sitest::iterator it = call_sites.begin();
          it != call_sites.end(); ++it)
  {
    // Collect the used summaries
    if (it->second.get_precision() != HAVOC) {
      summary_ids_sett new_summaries;
      const summary_ids_sett& old_summaries =
              it->second.get_used_summaries();
      
      for (summary_ids_sett::const_iterator it2 = old_summaries.begin();
              it2 != old_summaries.end(); ++it2)
      {
        new_summaries.insert(remap[*it2]);
      }
      
      it->second.set_used_summaries(new_summaries);
      
      // Propagate the call
      remap_used_summaries(it->second, remap);
    }
  }
}

/*******************************************************************\

Function: summary_storet::compact_store

  Inputs:

 Outputs:

 Purpose: Compacts the store representation, only representatives are kept

\*******************************************************************/

void summary_storet::compact_store(summary_infot& summary_info, 
        function_infost& function_infos)
{
  // Mask unused representatives
  bool *used_mask = new bool[max_id];
  memset(&used_mask, 0, sizeof(used_mask));
  
  mark_used_summaries(summary_info, used_mask);
  for (function_infost::iterator it = function_infos.begin();
          it != function_infos.end(); ++it) {
    const summary_idst& summaries = it->second.get_summaries();
    
    for (summary_idst::const_iterator it2 = summaries.begin();
            it2 != summaries.end(); ++it2)
    {
      assert (store[*it2].is_repr());
      used_mask[*it2] = true;
    }
  }
  
  // Fill remap for the representatives
  summary_idt* remap = new summary_idt[max_id];
  summary_idt new_id = 0;
  
  for (summary_idt i = 0; i < max_id; ++i) {
    if (store[i].is_repr() && used_mask[i]) {
      remap[i] = new_id++;
    }
  }
  
  // Fill remap for the rest
  for (summary_idt i = 0; i < max_id; ++i) {
    remap[i] = remap[store[i].repr_id];
  }
  
  // Remap and shrink

  remap_used_summaries(summary_info, remap);
  for (function_infost::iterator it = function_infos.begin();
          it != function_infos.end(); ++it) {
    summary_idst summaries;
    it->second.set_summaries(summaries);
    
    for (summary_idst::iterator it2 = summaries.begin();
            it2 != summaries.end(); ++it2)
    {
      *it2 = remap[*it2];
    }
    it->second.set_summaries(summaries);
  }
  
  storet new_store;
  new_store.reserve(new_id);
  for (summary_idt i = 0; i < max_id; ++i) {
    if (store[i].is_repr() && used_mask[i]) {
      store[i].repr_id = remap[i];
      new_store.push_back(store[i]);
    }
  }
  store.swap(new_store);
  
  max_id = new_id;
  repr_count = new_id;
  
  return;
}

