/*******************************************************************

 Module: Represents a block of SSA statements corresponding to 
 a single function.

 Author: Ondrej Sery

\*******************************************************************/

#ifndef CPROVER_PARTITION_H
#define	CPROVER_PARTITION_H

#include <goto-symex/symex_target_equation.h>

#include "summary_store_fwd.h"
#include "partition_fwd.h"
#include "solvers/interpolating_solver_fwd.h"

class partition_ifacet;

class partitiont {
public:
  static const int NO_PARTITION = -1;
  
  partitiont(partition_idt _parent_id, partition_ifacet& _partition_iface) :
          summary(false), stub(false), ignore(false), processed(false),
          fle_part_id(-1), parent_id(_parent_id), partition_iface(&_partition_iface) { }
          
  void add_child_partition(partition_idt child_id, unsigned callsite) {
    child_ids.push_back(child_id);
    child_locs.push_back(callsite);
  }
          
  // NOTE: This call is potentially slow: O(n)
  void remove_child_partition(partition_idt child_id) {
    assert (child_ids.size() == child_locs.size());
    partition_idst::iterator it1 = child_ids.begin();
    partition_locst::iterator it2 = child_locs.begin();
    
    while (*it1 != child_id) {
      ++it1;
      ++it2;
    }
    child_ids.erase(it1);
    child_locs.erase(it2);
  }

  void set_fle_part_id(fle_part_idt _fle_part_id) {
    fle_part_id = _fle_part_id;
  }
  
  partition_ifacet& get_iface() { return *partition_iface; }
  const partition_ifacet& get_iface() const { return *partition_iface; }

  bool is_inline(){
    return
        !(summary || stub || ignore);
       // || get_iface().assertion_in_subtree);
  }

  unsigned start_idx;
  // Index after the last SSA corresponding to this partition
  unsigned end_idx;
  symex_target_equationt::SSA_stepst::iterator start_it;
  // Iterator after the last SSA corresponding to this partition
  symex_target_equationt::SSA_stepst::iterator end_it;
  // if true, summaries should be used as representation of this partition
  bool summary;
  // if true, this partition represents havocing function
  bool stub;
  // if true, this partition was found to be redundant in slicing and should not be present in the resulting formula
  bool ignore;
  // if true, this partition has been symexed already (i.e. it has ssa representation in the equation already)
  bool processed;

  unsigned clauses;
  unsigned vars;
  // All summaries for the associated function
  summary_idst summaries;
  // Summaries that are applicable after slicing //MB: TODO investigate this
  summary_ids_sett applicable_summaries;
  // Summaries used in the previous verification
  fle_part_idt fle_part_id;
  partition_idt parent_id;
  partition_idst child_ids;
  partition_locst child_locs;

private:
  partition_ifacet* partition_iface;
};

#endif	/* CPROVER_PARTITION_H */

