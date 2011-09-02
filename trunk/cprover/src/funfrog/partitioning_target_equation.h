/*******************************************************************\

Module: Symex target equation which tracks different partitions for
different deferred functions.

Author: Ondrej Sery

\*******************************************************************/

#ifndef CPROVER_PARTITIONING_TARGET_EQUATION_H
#define CPROVER_PARTITIONING_TARGET_EQUATION_H

#include <goto-symex/symex_target_equation.h>
#include <symbol.h>

#include "partition_iface.h"
#include "summarization_context.h"

typedef std::vector<symex_target_equationt::SSA_stept*> SSA_steps_orderingt;

class partitioning_target_equationt:public symex_target_equationt
{
public:
  partitioning_target_equationt(const namespacet &_ns, summarization_contextt&
          _summarization_context) :
          symex_target_equationt(_ns), 
          summarization_context(_summarization_context),
          current_partition_id(partitiont::NO_PARTITION) {
  }

  // Convert all the SSA steps into the corresponding formulas in
  // the corresponding partitions
  void convert(prop_convt &prop_conv, interpolating_solvert &interpolator);

  // Reserve a partition id for later use. The newly reserved partition
  // will be dependent on the currently processed partition (if there is any).
  partition_idt reserve_partition(partition_ifacet& partition_iface)
  {
    partition_idt new_id = partitions.size();
    partition_idt parent_id = partition_iface.parent_id;

    partitions.push_back(partitiont(parent_id, partition_iface));

    bool check = partition_map.insert(partition_mapt::value_type(
      partition_iface.callend_symbol.get_identifier(), new_id)).second;
    assert(check);

    if (parent_id != partitiont::NO_PARTITION) {
      partitions[parent_id].add_child_partition(new_id, SSA_steps.size());
    }
    partition_iface.partition_id = new_id;

    return new_id;
  }
  
  // Marks the given partition as invalid. This is used in incremental SSA
  // generation to replace previously summarized partitions
  void invalidate_partition(partition_idt partition_id)
  {
    partitiont& partition = partitions[partition_id];
    
    partition.invalid = true;
    partition_map.erase(partition.get_iface().callend_symbol.get_identifier());
    
    if (partition.parent_id != partitiont::NO_PARTITION) {
      partitions[partition.parent_id].remove_child_partition(partition_id);
    }
  }

  // Fill the (reserved) partition with the given summaries.
  void fill_summary_partition(partition_idt partition_id,
    const summary_idst* summaries)
  {
    partitiont& sum_partition = partitions.at(partition_id);
    assert(!sum_partition.filled);

    sum_partition.filled = true;
    sum_partition.is_summary = true;
    sum_partition.summaries = summaries;
  }

  // Begin processing of the given (previously reserved) partition.
  // The following SSA statements will be part of the given partition until
  // a different partition is selected.
  void select_partition(partition_idt partition_id) {
    if (current_partition_id != partitiont::NO_PARTITION) {
      get_current_partition().end_idx = SSA_steps.size();
      assert(!partitions.at(partition_id).filled);
    }
    // Select the new partition
    current_partition_id = partition_id;
    partitiont& new_partition = get_current_partition();
    new_partition.filled = true;
    new_partition.start_idx = SSA_steps.size();
  }
  
  // Collects information about the specified partitions for later
  // processing and conversion
  void prepare_partitions();

  // Extract interpolants corresponding to the created partitions
  void extract_interpolants(
    interpolating_solvert& interpolator, const prop_convt& decider,
    interpolant_mapt& interpolant_map, double reduction_timeout = 0);
  
  // Returns SSA steps ordered in the order of program execution (i.e., as they 
  // would be normally ordered in symex_target_equation).
  const SSA_steps_orderingt& get_steps_exec_order() {
    if (SSA_steps_exec_order.size() != SSA_steps.size()) {
      // Prepare SSA ordering according to the program execution order.
      assert(!partitions.empty());
      SSA_steps_exec_order.clear();
      SSA_steps_exec_order.reserve(SSA_steps.size());
      prepare_SSA_exec_order(partitions[0]);
      assert(SSA_steps_exec_order.size() == SSA_steps.size());
    }
    return SSA_steps_exec_order;
  }
  
  partitionst& get_partitions() { return partitions; }

  bool any_applicable_summaries() {
    for (unsigned i = 0; i < partitions.size(); i++) {
      if (!partitions[i].applicable_summaries.empty()) {
        return true;
      }
    }
    return false;
  }

private:
  // Current summarization context
  summarization_contextt& summarization_context;
  
  // Id of the currently selected partition
  partition_idt current_partition_id;
  
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
  // Convert a summary partition (i.e., assert its summary)
  void convert_partition_summary(prop_convt &prop_conv,
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

  // Fills in the list of symbols that the partition has in common with its
  // environment
  void fill_common_symbols(const partitiont& partition,
    std::vector<symbol_exprt>& common_symbols) const
  {
    common_symbols.clear();
    const partition_ifacet& iface = partition.get_iface();
    common_symbols.reserve(iface.argument_symbols.size() + 
      iface.out_arg_symbols.size()+4);
    common_symbols = iface.argument_symbols;
    common_symbols.insert(common_symbols.end(), 
      iface.out_arg_symbols.begin(),
      iface.out_arg_symbols.end());
    common_symbols.push_back(iface.callstart_symbol);
    common_symbols.push_back(iface.callend_symbol);
    if (iface.assertion_in_subtree) {
      common_symbols.push_back(iface.error_symbol);
    }
    if (iface.returns_value) {
      common_symbols.push_back(iface.retval_symbol);
    }
  }

  // Fill in ids of all the child partitions
  void fill_partition_ids(partition_idt partition_id, fle_part_idst& part_ids);

  // Fills in the SSA_steps_exec_order holding pointers to SSA steps ordered
  // in the order of program execution (i.e., as they would be normally 
  // ordered in symex_target_equation).
  void prepare_SSA_exec_order(const partitiont& partition);
  
  // Find partition corresponding to the function call. 
  // If the given SSA step is a callend assumption, the corresponding target 
  // partition is returned. If not, NULL is returned.
  const partitiont* find_target_partition(const SSA_stept& step);
  
  // Collection of all the partitions
  partitionst partitions;
  
  // Mapping between callend symbol and the corresponding partition
  // This is used to emit assumption propagation constraints.
  partition_mapt partition_map;
  
  // Ordering of SSA steps according to the program execution order, this is
  // filled in by prepare_SSA_exec_order and can be used for simple slicing
  // and error trace generation.
  // NOTE: Currently, the order is slightly broken by the glue variables
  SSA_steps_orderingt SSA_steps_exec_order;
  
  friend class partitioning_slicet;
};

#endif
