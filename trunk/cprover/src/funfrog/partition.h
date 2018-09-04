/*******************************************************************

 Module: Represents a block of SSA statements corresponding to 
 a single function.

\*******************************************************************/

#ifndef CPROVER_PARTITION_H
#define	CPROVER_PARTITION_H

#include "summary_store_fwd.h"
#include "partition_fwd.h"
#include "solvers/interpolating_solver_fwd.h"
#include "partition_representation.h"
#include "utils/containers_utils.h"

#include <goto-symex/symex_target_equation.h>



class partition_ifacet;

class partitiont {
public:
  
  partitiont(partition_idt _parent_id, partition_ifacet& _partition_iface) :
          ignore(false),
//          converted(false),
          parent_id(_parent_id),
          representation(partition_representation::NONE),
          partition_iface(&_partition_iface) { }
          
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

  void add_fle_part_id(fle_part_idt _fle_part_id) {
    assert(!contains(fle_part_indices, _fle_part_id));
    this->fle_part_indices.push_back(_fle_part_id);
  }

  const std::vector<fle_part_idt>& get_fle_part_ids(){
      return this->fle_part_indices;
  }

  void event_solver_reseted(){
      this->fle_part_indices.clear();
  }
  
  partition_ifacet& get_iface() { return *partition_iface; }
  const partition_ifacet& get_iface() const { return *partition_iface; }

  unsigned start_idx;
  // Index after the last SSA corresponding to this partition
  unsigned end_idx;
  symex_target_equationt::SSA_stepst::iterator start_it;
  // Iterator after the last SSA corresponding to this partition
  symex_target_equationt::SSA_stepst::iterator end_it;

  // =========== PARTITION FLAGS ==============================
  // if true, this partition was found to be redundant in slicing and should not be present in the resulting formula
  bool ignore;
  // if true, this partition had already its current representation converted
//  bool converted;

  bool has_ssa_representation() const {return (representation & partition_representation::SSA) == partition_representation::SSA;}
  bool is_real_ssa_partition() const {return has_ssa_representation() && !has_abstract_representation();}
  bool has_abstract_representation() const {
      return (representation & (partition_representation::STUB | partition_representation::SUMMARY)) != partition_representation::NONE;
  } // such partition can be refined to have more precise representation
    bool has_no_representation () const {return representation == partition_representation ::NONE;}
    bool is_stub() const {
      return representation == partition_representation ::STUB;}
    bool has_summary_representation () const {
        return (representation & partition_representation::SUMMARY) != partition_representation::NONE;}

  void remove_abstract_representation(){
      representation = representation & ~(partition_representation::STUB | partition_representation::SUMMARY);
  }
  void add_summary_representation() {representation = (representation | partition_representation ::SUMMARY);}
  void add_stub_representation() {
      assert(representation == partition_representation::NONE); // stub should not be combined with anything
      representation = (representation | partition_representation ::STUB);
  }
  void add_ssa_representation() {representation = (representation | partition_representation ::SSA);}

 // =========== PARTITION FLAGS ==============================

  // All summaries for the associated function
  summary_idst summaries;
  // Summaries that are applicable after slicing //MB: TODO investigate this
  summary_ids_sett applicable_summaries;

//  fle_part_idt fle_part_id;
  partition_idt parent_id;
  partition_idst child_ids;
  partition_locst child_locs;

    inline bool has_parent() const { return parent_id != NO_PARTITION_ID; }

private:
    partition_representation representation;
    partition_ifacet * partition_iface;
    std::vector<fle_part_idt> fle_part_indices;

};

#endif	/* CPROVER_PARTITION_H */

