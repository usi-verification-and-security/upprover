/*******************************************************************\

Module: Storage class for function summaries (union-find).

Author: Ondrej Sery

\*******************************************************************/

#include "summary_store.h"
#include "summary_info.h"

const summary_storet::nodet& summary_storet::find_repr(summary_idt id) const
{
  const nodet& node = store[id];
  
  if (node.is_repr()) {
    return node;
  }

  assert(node.repr_id != id);
  
  const summary_storet::nodet& repr_node = find_repr(node.repr_id);
//  node.update_repr(repr_node.repr_id);
  
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

summaryt& summary_storet::find_summary(summary_idt new_id) const
{
  const nodet& node = find_repr(new_id);
  
  return *(node.summary);
}



