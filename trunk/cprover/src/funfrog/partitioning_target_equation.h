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
#include "solvers/smtcheck_opensmt2.h"

typedef std::vector<symex_target_equationt::SSA_stept*> SSA_steps_orderingt;

typedef enum {
  NO_COLORING,
  RANDOM_COLORING,
  COLORING_FROM_FILE,
  TBD
  // anything else?
}
  coloring_modet;

class partitioning_target_equationt:public symex_target_equationt
{
public:
  partitioning_target_equationt(const namespacet &_ns, summarization_contextt&
          _summarization_context, bool _upgrade_checking,
          bool _store_summaries_with_assertion, coloring_modet _coloring_mode,
          std::vector<unsigned>& _clauses) :
          symex_target_equationt(_ns),
          summarization_context(_summarization_context),
          current_partition_id(partitiont::NO_PARTITION),
          upgrade_checking(_upgrade_checking),
          store_summaries_with_assertion(_store_summaries_with_assertion),
          coloring_mode(_coloring_mode),
          clauses(_clauses),
		  out_local_terms(0),
		  out_terms(out_local_terms),
		  out_local_basic(0),
		  out_basic(out_local_basic),
		  out_local_partition(0),
		  out_partition(out_local_partition),
		  terms_counter(0),
		  is_first_call(true),
		  first_call_expr(0)
		  {
	  partition_smt_decl = new std::map <std::string,exprt>();
	  out_terms.rdbuf(&terms_buf);
	  out_basic.rdbuf(&basic_buf);
	  out_partition.rdbuf(&partition_buf);

  }

  // First this called and then the parent d'tor due to the use of virtual
  virtual ~partitioning_target_equationt() {
	  partition_smt_decl->clear();
	  delete partition_smt_decl;
	  first_call_expr = 0; // Not here to do the delete
  }

  // Convert all the SSA steps into the corresponding formulas in
  // the corresponding partitions
  void convert(smtcheck_opensmt2t &decider, interpolating_solvert &interpolator);

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
      partitions[parent_id].add_child_partition(new_id, partition_iface.call_loc);
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
    sum_partition.summary = true;
    sum_partition.summaries = summaries;

    sum_partition.applicable_summaries.clear();
    for (summary_idst::const_iterator it = summaries->begin();
            it != summaries->end();
            ++it) {
      sum_partition.applicable_summaries.insert(*it);
    }
  }

  // Fill the (reserved) partition with the stub summary.
  void fill_stub_partition(partition_idt partition_id)
  {
    partitiont& sum_partition = partitions.at(partition_id);
    assert(!sum_partition.filled);

    sum_partition.filled = true;
    sum_partition.stub = true;

  }

  // Fill the (reserved) partition with the given summaries.
  void fill_inverted_summary_partition(partition_idt partition_id,
    const summary_idst* summaries, const summary_ids_sett& used_summaries)
  {
    partitiont& sum_partition = partitions.at(partition_id);
    assert(!sum_partition.filled);

    sum_partition.filled = true;
    sum_partition.summary = true;
    sum_partition.inverted_summary = true;
    sum_partition.summaries = summaries;
    sum_partition.used_summaries = used_summaries;
    sum_partition.applicable_summaries = used_summaries;

    std::cerr << "  --- (" << partition_id <<
            ") sums: " << sum_partition.summaries->size() <<
            " used: " << sum_partition.used_summaries.size() << std::endl;
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
    interpolating_solvert& interpolator, const smtcheck_opensmt2t& decider,
    interpolant_mapt& interpolant_map);

  // Returns SSA steps ordered in the order of program execution (i.e., as they
  // would be normally ordered in symex_target_equation).
  const SSA_steps_orderingt& get_steps_exec_order() {
    if (SSA_steps_exec_order.size() != SSA_steps.size()) {
      // Prepare SSA ordering according to the program execution order.
      assert(!partitions.empty());
      SSA_steps_exec_order.clear();
      SSA_steps_exec_order.reserve(SSA_steps.size());
      prepare_SSA_exec_order(partitions[0]);
      //FIXME: assertion simply doesn't hold if there were some summaries substituted
      //assert(SSA_steps_exec_order.size() == SSA_steps.size());
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

  unsigned get_SSA_steps_count() const { return SSA_steps.size(); }

private:
  // Current summarization context
  summarization_contextt& summarization_context;

  // Id of the currently selected partition
  partition_idt current_partition_id;

  // For SMT-Lib Translation - Move it later to a new class
  std::map <std::string,exprt>* partition_smt_decl;
  std::ostream out_local_terms; //for prints SSA - remove later
  std::ostream& out_terms; // for prints SSA - remove later
  std::stringbuf terms_buf; // for prints SSA - remove later

  std::ostream out_local_basic; //for prints SSA - remove later
  std::ostream& out_basic; // for prints SSA - remove later
  std::stringbuf basic_buf; // for prints SSA - remove later

  std::ostream out_local_partition; //for prints SSA - remove later
  std::ostream& out_partition; // for prints SSA - remove later
  std::stringbuf partition_buf; // for prints SSA - remove later

  int terms_counter; // for prints SSA - remove later
  bool is_first_call; // for prints SSA - remove later
  const exprt* first_call_expr; // for prints SSA - remove later

  // Print decl (later change to create)
  std::ostream& print_decl_smt(std::ostream& out);
  void print_all_partition(std::ostream& out);
  void print_partition();
  void addToDeclMap(const exprt &expr);
  void saveFirstCallExpr(const exprt& expr);
  bool isFirstCallExpr(const exprt& expr);
  void getFirstCallExpr();

  // Convert a specific partition of SSA steps
  void convert_partition(smtcheck_opensmt2t &decider,
    interpolating_solvert &interpolator, partitiont& partition);
  // Convert a specific partition guards of SSA steps
  void convert_partition_guards(smtcheck_opensmt2t &decider,
    partitiont& partition);
  // Convert a specific partition assignments of SSA steps
  void convert_partition_assignments(smtcheck_opensmt2t &decider,
    partitiont& partition);
  // Convert a specific partition assumptions of SSA steps
  void convert_partition_assumptions(smtcheck_opensmt2t &decider,
    partitiont& partition);
  // Convert a specific partition assertions of SSA steps
  void convert_partition_assertions(smtcheck_opensmt2t &decider,
    partitiont& partition);
  // Convert a specific partition io of SSA steps
  void convert_partition_io(smtcheck_opensmt2t &decider,
    partitiont& partition);
  // Convert a summary partition (i.e., assert its summary)
  void convert_partition_summary(smtcheck_opensmt2t &decider,
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

  // Mode of encoding. Are we doing upgrade check?
  bool upgrade_checking;
  // Should we store summaries with assertion in subtree?
  // This is used in upgrade checking.
  bool store_summaries_with_assertion;

  coloring_modet coloring_mode;

  std::vector<unsigned>& clauses;

  friend class partitioning_slicet;
};

#endif
