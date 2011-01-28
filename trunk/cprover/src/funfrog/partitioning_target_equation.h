/*******************************************************************\

Module: Symex target equation which tracks different partitions for
different deferred functions.

Author: Ondrej Sery

\*******************************************************************/

#ifndef CPROVER_PARTITIONING_TARGET_EQUATION_H
#define CPROVER_PARTITIONING_TARGET_EQUATION_H

#include <goto-symex/symex_target_equation.h>

#include "interpolation/interpolating_solver.h"

typedef int partition_idt;
typedef std::vector<partition_idt> partition_idst;

class partitioning_target_equationt:public symex_target_equationt
{
public:
  static const int NO_PARTITION = -1;

  partitioning_target_equationt(const namespacet &_ns) :
          symex_target_equationt(_ns), current_partition_id(NO_PARTITION) {
  }

  // Convert all the SSA steps into the corresponding formulas in
  // the corresoponding partitions
  void convert(prop_convt &prop_conv);

  // Reserve a partition id for later use. The newly reserved partition
  // will be dependent on the currently processed partition (if there is any).
  partition_idt reserve_partition() {
    partition_idt new_id = partitions.size();

    partitions.push_back(partitiont(current_partition_id));
    get_current_partition().add_child_partition(new_id);

    return new_id;
  }

  // Begin processing of the given (previously reserved) partition.
  // The follwoing SSA statements will be part of the given partition until
  // a different partition is selected.
  void select_partition(partition_idt partition_id) {
    get_current_partition().end_idx = SSA_steps.size() - 1;

    assert(!partitions.at(partition_id).filled);

    // Select the new partition
    current_partition_id = partition_id;
    partitiont& new_partition = get_current_partition();
    new_partition.filled = true;
    new_partition.start_idx = SSA_steps.size();
  }

private:
  
  // Represents nesting of partitions
  class partitiont {
  public:
    partitiont(partition_idt _parent_id) : 
            filled(false), parent_id(_parent_id) {}

    void add_child_partition(partition_idt child_id) {
      child_ids.push_back(child_id);
    }
    void set_fle_part_id(fle_part_idt _fle_part_id) {
      fle_part_id = _fle_part_id;
    }
    const partition_idst& get_partition_ids() const { return child_ids; }

    bool filled;
    int start_idx;
    int end_idx;

  private:
    fle_part_idt fle_part_id;
    partition_idt parent_id;
    partition_idst child_ids;
  };

  // Safe getter for the current partition
  partitiont& get_current_partition() {
    if (partitions.empty()) {
      // If there is no partition yet, we will create a dummy one. There will
      // be no means for getting the corresponding interpolant.
      select_partition(reserve_partition());
    }

    return partitions[current_partition_id];
  }

  typedef std::vector<partitiont> partitionst;
  // Collection of all the partitions
  partitionst partitions;
  
  // Id of the currently selected partition
  partition_idt current_partition_id;
};

#endif
