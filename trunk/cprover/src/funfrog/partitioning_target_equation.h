/*******************************************************************\

Module: Symex target equation which tracks different partitions for
different deferred functions.

Author: Ondrej Sery

\*******************************************************************/

#ifndef CPROVER_PARTITIONING_TARGET_EQUATION_H
#define CPROVER_PARTITIONING_TARGET_EQUATION_H

// Debugging flags:
//#define DEBUG_SSA // General debug prints
//#define DEBUG_ENCODING
//#define DEBUG_SSA_SMT_CALL // Before call to smt interface add a debug print
// End of working debugging flags

#include <util/symbol.h>
#ifdef DISABLE_OPTIMIZATIONS
#include <iostream>
#include "expr_pretty_print.h"
#endif

#include <goto-symex/symex_target_equation.h>
#include "summary_store_fwd.h"
#include "solvers/interpolating_solver_fwd.h"
#include "partition.h"

class partition_ifacet;
class check_opensmt2t;
class interpolating_solvert;

typedef std::vector<symex_target_equationt::SSA_stept*> SSA_steps_orderingt;

class partitioning_target_equationt:public symex_target_equationt
{
public:
  partitioning_target_equationt(const namespacet &_ns, summary_storet & summary_store,
                                bool _store_summaries_with_assertion);

  // First this called and then the parent d'tor due to the use of virtual
  virtual ~partitioning_target_equationt() {
#         ifdef DISABLE_OPTIMIZATIONS        
	  partition_smt_decl->clear();
	  delete partition_smt_decl;        
	  first_call_expr = 0; // Not here to do the delete
#         endif
  }

  // Reserve a partition id for later use. The newly reserved partition
  // will be dependent on the currently processed partition (if there is any).
  partition_idt reserve_partition(partition_ifacet& partition_iface);

  // Marks the given partition as invalid. This is used in incremental SSA
  // generation to replace previously summarized partitions
  void invalidate_partition(partition_idt partition_id);

    void refine_partition(partition_idt partition_id);

  // Fill the (reserved) partition with the given summaries.
  void fill_summary_partition(partition_idt partition_id, const summary_idst & summaries);

  // Fill the (reserved) partition with the stub summary.
  void fill_stub_partition(partition_idt partition_id);

  // Fill the (reserved) partition with the given summaries.
  void fill_inverted_summary_partition(partition_idt partition_id,
    const summary_idst* summaries, const summary_ids_sett& used_summaries);

  // Begin processing of the given (previously reserved) partition.
  // The following SSA statements will be part of the given partition until
  // a different partition is selected.
  void select_partition(partition_idt partition_id);

  // Collects information about the specified partitions for later
  // processing and conversion
  void prepare_partitions();

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

  virtual void extract_interpolants(check_opensmt2t& decider) = 0;

  virtual void convert(check_opensmt2t &prop_conv, interpolating_solvert &interpolator) = 0;

  partitionst& get_partitions() { return partitions; }

  unsigned get_SSA_steps_count() const { return SSA_steps.size(); }
 
#ifdef DISABLE_OPTIMIZATIONS  
  void set_dump_SSA_tree(bool f) { dump_SSA_tree = f;}
  void set_dump_SSA_tree_name(const std::string& n)
  {
    ssa_tree_file_name = "__SSA_" + n;
  }
#endif
  
protected:

  // Id of the currently selected partition
  partition_idt current_partition_id;

#ifdef DISABLE_OPTIMIZATIONS  
  // KE: shall go to the reporter class!
  // FIXME: move to SSA_Reportert class
  bool dump_SSA_tree;
  std::string ssa_tree_file_name;
  
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
  void saveFirstCallExpr(const exprt& expr);
  bool isFirstCallExpr(const exprt& expr);
  void getFirstCallExpr();
#endif
  unsigned io_count_global; // KE: for Inputs in SSA expression - new CProver version can have more than one input entry

  unsigned count_partition_assertions(const partitiont& partition) const;

  // Safe getter for the current partition
  partitiont& get_current_partition() {
    return partitions[current_partition_id];
  }

  // Fills in the list of symbols that the partition has in common with its
  // environment
  virtual void fill_common_symbols(const partitiont& partition,
    std::vector<symbol_exprt>& common_symbols) const;

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

  virtual void goto_instruction(
    const exprt &guard,
    const exprt &cond,
    const sourcet &source) override {}

    void close_current_partition();


  summary_storet & summary_store;
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

  // Should we store summaries with assertion in subtree?
  // This is used in upgrade checking.
  bool store_summaries_with_assertion;

  friend class partitioning_slicet;
};

#endif
