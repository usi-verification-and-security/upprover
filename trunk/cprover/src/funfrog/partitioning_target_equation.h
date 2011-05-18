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
typedef std::list<partition_idt> partition_idst;
typedef std::list<unsigned> partition_locst;
typedef std::vector<symex_target_equationt::SSA_stept*> SSA_steps_orderingt;

class partitioning_target_equationt:public symex_target_equationt
{
public:
  static const int NO_PARTITION = -1;

  partitioning_target_equationt(const namespacet &_ns) :
          symex_target_equationt(_ns), current_partition_id(NO_PARTITION) {
  }

  // Convert all the SSA steps into the corresponding formulas in
  // the corresponding partitions
  void convert(prop_convt &prop_conv, interpolating_solvert &interpolator);

  // Reserve a partition id for later use. The newly reserved partition
  // will be dependent on the currently processed partition (if there is any).
  partition_idt reserve_partition(
    const symbol_exprt& callstart_symbol,
    const symbol_exprt& callend_symbol,
    const std::vector<symbol_exprt>& argument_symbols,
    const std::vector<symbol_exprt>& out_arg_symbols,
    const symbol_exprt& retval_symbol,
    bool returns_value,
    irep_idt function_id)
  {
    partition_idt new_id = partitions.size();

    partitions.push_back(partitiont(current_partition_id));
    partitiont& new_partition = partitions.back();

    new_partition.callstart_symbol = callstart_symbol;
    new_partition.callend_symbol = callend_symbol;
    new_partition.argument_symbols = argument_symbols;
    new_partition.out_arg_symbols = out_arg_symbols;
    new_partition.retval_symbol = retval_symbol;
    new_partition.returns_value = returns_value;
    new_partition.function_id = function_id;
    partition_map.insert(partition_mapt::value_type(
      callend_symbol.get_identifier(), new_id));

    if (current_partition_id != NO_PARTITION) {
      get_current_partition().add_child_partition(new_id, SSA_steps.size());
    }

    return new_id;
  }

  // Fill the (reserved) partition with the given summaries.
  void fill_summary_partition(partition_idt partition_id,
    const interpolantst* summaries)
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

  bool any_applicable_summaries() { /* FIXME:
	  for (unsigned i = 0; i < partitions.size(); i++) {
		  if (!partitions[i].applicable_summaries.empty()) {
			  return true;
		  }
	  }
	  return false;*/
	  return true;
  }

private:
  
  // Represents nesting of partitions
  class partitiont {
  public:
    partitiont(partition_idt _parent_id) : 
            filled(false), is_summary(false), ignore(false), processed(false), 
            summaries(NULL), parent_id(_parent_id) {}

    void add_child_partition(partition_idt child_id, unsigned callsite) {
      child_ids.push_back(child_id);
      child_locs.push_back(callsite);
    }
    void set_fle_part_id(fle_part_idt _fle_part_id) {
      fle_part_id = _fle_part_id;
    }

    bool filled;
    unsigned start_idx;
    // Index after the last SSA corresponding to this partition
    unsigned end_idx;
    SSA_stepst::iterator start_it;
    // Iterator after the last SSA corresponding to this partition
    SSA_stepst::iterator end_it;
    symbol_exprt callstart_symbol;
    symbol_exprt callend_symbol;
    std::vector<symbol_exprt> argument_symbols;
    std::vector<symbol_exprt> in_arg_symbols;
    std::vector<symbol_exprt> out_arg_symbols;
    symbol_exprt retval_symbol;
    bool returns_value;
    bool is_summary;
    bool ignore;
    bool processed;
    const interpolantst* summaries;
    hash_set_cont<unsigned> applicable_summaries;
    literalt callstart_literal;
    literalt callend_literal;
    fle_part_idt fle_part_id;
    partition_idt parent_id;
    partition_idst child_ids;
    partition_locst child_locs;
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
    common_symbols.reserve(partition.argument_symbols.size() + 
      partition.out_arg_symbols.size()+3);
    common_symbols = partition.argument_symbols;
    common_symbols.insert(common_symbols.end(), 
      partition.out_arg_symbols.begin(),
      partition.out_arg_symbols.end());
    common_symbols.push_back(partition.callstart_symbol);
    common_symbols.push_back(partition.callend_symbol);
    if (partition.returns_value) {
      common_symbols.push_back(partition.retval_symbol);
    }
  }

  // Fill in ids of all the child partitions
  void fill_partition_ids(partition_idt partition_id, fle_part_idst& part_ids);

  // Fills in the SSA_steps_exec_order holding pointers to SSA steps ordered
  // in the order of program execution (i.e., as they would be normally 
  // ordered in symex_target_equation).
  void prepare_SSA_exec_order(const partitiont& partition);
  
  typedef std::vector<partitiont> partitionst;
  typedef std::map<irep_idt, partition_idt> partition_mapt;
  
  // Collection of all the partitions
  partitionst partitions;
  
  // Mapping between callend symbol and the corresponding partition
  // This is used to emit assumption propagation constraints.
  partition_mapt partition_map;
  
  // Id of the currently selected partition
  partition_idt current_partition_id;

  // Ordering of SSA steps according to the program execution order, this is
  // filled in by prepare_SSA_exec_order and can be used for simple slicing
  // and error trace generation.
  // NOTE: Currently, the order is slightly broken by the glue variables
  SSA_steps_orderingt SSA_steps_exec_order;
  
  friend class partitioning_slicet;
};

#endif
