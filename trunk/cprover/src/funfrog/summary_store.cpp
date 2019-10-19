/*******************************************************************\

Module: Storage class for function summaries (union-find).

\*******************************************************************/

#include "summary_store.h"
#include "call_tree_node.h"
#include <algorithm>

const summary_storet::nodet& summary_storet::find_repr(summary_idt id) const
{
    assert(id >= 0 && id < store.size());
    const nodet& node = store[id];
    return node;

//  assert(node.id != id);
//
//  const summary_storet::nodet& repr_node = find_repr(node.id);
////  node.update_repr(repr_node.repr_id);
//  return repr_node;
}

/*******************************************************************\

Function: summary_storet::replace_summary

  Inputs:

 Outputs:

 Purpose: An already stored summary is implied by the new one - it is released
 and represented by the stronger one, the id is still valid but represented
 by the new one.

\*******************************************************************/

//void summary_storet::replace_summary(summary_idt old_summary_id,
//        summary_idt replacement_id)
//{
//  nodet& node = store[old_summary_id];
//
//  assert(old_summary_id != replacement_id);
//  assert(node.is_repr());
//  assert(find_repr(replacement_id).repr_id != old_summary_id);
//
//  node.update_repr(replacement_id);
//
//  repr_count--;
//}

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

summaryt& summary_storet::find_summary(summary_idt new_id) const
{
  const nodet& node = find_repr(new_id);
  
  return *(node.summary);
}

/*******************************************************************\

Function: summary_storet::insert_summary

  Inputs:

 Outputs:

 Purpose: Inserts a new summary, summary store takes ownership of the pointer; the passed pointer cannot be used anymore!

\*******************************************************************/
summary_idt summary_storet::insert_summary(summaryt * summary_given, const std::string & function_name) {
    // Do not add summary if the same is already there
    if(has_summaries(function_name)) {
        const auto & summaries = get_summariesID(function_name);
        auto it = std::find_if(summaries.begin(), summaries.end(), [this, summary_given](summary_idt id){
            return find_summary(id).equals(summary_given);
        });
        if(it != summaries.end()){
            summary_idt id = *it;
            // the same summary for this function is already present in the store
            // delete the summary;
            delete summary_given;
            return id;
        }
    }
    // TODO optimizations of summary store? Do we want to check for stronger summaries and replace the weaker ones?
    summary_idt new_id = max_id++;
    store.emplace_back(new_id, summary_given);
    // this also creates the map entry if it is the first time we see this function_name
    function_to_summaries[function_name].push_back(new_id);
    repr_count++;
    return new_id;
}
/*******************************************************************
 Purpose: store summaries into a given file
\*******************************************************************/

void summary_storet::serialize(std::string file_name) {
    std::ofstream out;
    out.open(file_name);
    this->serialize(out);
    out.close();
}
