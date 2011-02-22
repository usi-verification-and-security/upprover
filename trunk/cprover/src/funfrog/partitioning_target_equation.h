/*******************************************************************\

Module: Symex target equation which tracks different partitions for
different deferred functions.

Author: Ondrej Sery

\*******************************************************************/

#ifndef CPROVER_PARTITIONING_TARGET_EQUATION_H
#define CPROVER_PARTITIONING_TARGET_EQUATION_H

#include <goto-symex/symex_target_equation.h>
#include <symbol.h>

#include "solvers/interpolating_solver.h"

typedef int partition_idt;
typedef std::vector<partition_idt> partition_idst;
typedef std::vector<std::pair<irep_idt, prop_itpt> > interpolant_mapt;

class partitioning_target_equationt:public symex_target_equationt
{
public:
  static const int NO_PARTITION = -1;

  partitioning_target_equationt(const namespacet &_ns) :
          symex_target_equationt(_ns), current_partition_id(NO_PARTITION) {
  }

  // Convert all the SSA steps into the corresponding formulas in
  // the corresoponding partitions
  void convert(prop_convt &prop_conv, interpolating_solvert &interpolator);

  // Reserve a partition id for later use. The newly reserved partition
  // will be dependent on the currently processed partition (if there is any).
  partition_idt reserve_partition(
    const symbol_exprt& callstart_symbol,
    const symbol_exprt& callend_symbol,
    irep_idt function_id)
  {
    partition_idt new_id = partitions.size();

    partitions.push_back(partitiont(current_partition_id));
    partitiont& new_partition = partitions.back();

    new_partition.callstart_symbol = callstart_symbol;
    new_partition.callend_symbol = callend_symbol;
    new_partition.function_id = function_id;
    partition_map.insert(partition_mapt::value_type(
      callend_symbol.get_identifier(), new_id));

    if (current_partition_id != NO_PARTITION)
      get_current_partition().add_child_partition(new_id);

    return new_id;
  }

  // Begin processing of the given (previously reserved) partition.
  // The follwoing SSA statements will be part of the given partition until
  // a different partition is selected.
  void select_partition(partition_idt partition_id) {
    if (current_partition_id != NO_PARTITION) {
      get_current_partition().end_idx = SSA_steps.size();
      assert(!partitions.at(partition_id).filled);
    }

    // Select the new partition
    current_partition_id = partition_id;
    partitiont& new_partition = get_current_partition();
    new_partition.filled = true;
    new_partition.start_idx = SSA_steps.size();
  }
  
  // Collects information about the specified partions for later
  // processing and conversion
  void prepare_partitions();

  // Extract interpolants corresponding to the created partitions
  void extract_interpolants(interpolating_solvert& interpolator,
    interpolant_mapt& interpolant_map);

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
    // Index after the last SSA coresponding to this partition
    int end_idx;
    SSA_stepst::iterator start_it;
    // Iterator after the last SSA coresponding to this partition
    SSA_stepst::iterator end_it;
    symbol_exprt callstart_symbol;
    symbol_exprt callend_symbol;
    literalt callstart_literal;
    literalt callend_literal;
    fle_part_idt fle_part_id;
    partition_idt parent_id;
    partition_idst child_ids;
    irep_idt function_id;
  };

  // Convert a specific partition of SSA steps
  void convert_partition(prop_convt &prop_conv,
    interpolating_solvert &interpolator, partitiont& partition);
  // Convert a specific partition guards of SSA steps
  void convert_partition_guards(prop_convt &prop_conv,
    partitiont& partition);
  // Convert a specific partition assignments of SSA steps
  void convert_partition_assignments(prop_convt &prop_conv,
    partitiont& partition) const;
  // Convert a specific partition assumptions of SSA steps
  void convert_partition_assumptions(prop_convt &prop_conv,
    partitiont& partition);
  // Convert a specific partition assertions of SSA steps
  void convert_partition_assertions(prop_convt &prop_conv,
    partitiont& partition);
  // Convert a specific partition io of SSA steps
  void convert_partition_io(prop_convt &prop_conv,
    partitiont& partition);

  unsigned count_partition_assertions(partitiont& partition) const
  {
    unsigned i=0;
    for(SSA_stepst::const_iterator
        it = partition.start_it;
        it != partition.end_it; it++)
      if(it->is_assert()) i++;
    return i;
  }

  // Safe getter for the current partition
  partitiont& get_current_partition() {
    return partitions[current_partition_id];
  }

  // Fill in ids of all the child partitions
  void fill_partition_ids(partition_idt partition_id, fle_part_idst& part_ids);

  typedef std::vector<partitiont> partitionst;
  typedef std::map<irep_idt, partition_idt> partition_mapt;
  // Collection of all the partitions
  partitionst partitions;
  // Mapping between callend symbol and the corresponding parititon
  // This is used to emit assumption propagation constraints.
  partition_mapt partition_map;
  
  // Id of the currently selected partition
  partition_idt current_partition_id;
};

#endif
