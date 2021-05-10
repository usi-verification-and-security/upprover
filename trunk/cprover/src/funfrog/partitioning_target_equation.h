/*******************************************************************\

Module: Symex target equation which tracks different partitions for
different deferred functions.

 The output of symbolic execution is a system of equations, asserations
 and assumptions; an object of type symex_target_equationt, containing
 a list of  CPROVER::symex_target_equationt::SSA_stept,
 each of which are equalities between exprt expressions.
 --This class provides Implementation of functions to build SSA equation
\*******************************************************************/

#ifndef CPROVER_PARTITIONING_TARGET_EQUATION_H
#define CPROVER_PARTITIONING_TARGET_EQUATION_H

#include <util/symbol.h>
#ifdef DISABLE_OPTIMIZATIONS
#include <sstream>
#include "expr_pretty_print.h"
#endif

#include <goto-symex/symex_target_equation.h>
#include <funfrog/interface/convertor.h>
#include "summary_store_fwd.h"
#include "solvers/interpolating_solver_fwd.h"
#include "partition.h"
#include "call_tree_node.h"

class partition_ifacet;
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
  //void invalidate_partition(partition_idt partition_id);

  void refine_partition(partition_idt partition_id);

  // Fill the (reserved) partition with the given summaries.
  void fill_summary_partition(partition_idt partition_id, const std::string & function_id);
  
  void fill_summary_partition(partition_idt partition_id, call_tree_nodet & node);
    
    // Fill the (reserved) partition with the stub summary.
  void fill_stub_partition(partition_idt partition_id);

  // Begin processing of the given (previously reserved) partition.
  // The following SSA statements will be part of the given partition until
  // a different partition is selected.
  void select_partition(partition_idt partition_id);

  // Collects information about the specified partitions for later
  // processing and conversion
  void prepare_partitions();

  // Returns SSA steps ordered in the order of program execution (i.e., as they
  // would be normally ordered in symex_target_equation). //it is needed for building error trace
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

  void extract_interpolants(interpolating_solvert &interpolator);

  void convert(convertort &prop_conv, interpolating_solvert &interpolator);

  partitionst& get_partitions() { return partitions; }

  unsigned get_SSA_steps_count() const { return SSA_steps.size(); }

  std::vector<exprt> get_exprs_to_refine();

  const summary_storet & get_summary_store() const { return summary_store; }

  void fill_function_templates(interpolating_solvert &interpolator, std::vector<itpt_summaryt*>& templates);
 
#ifdef DISABLE_OPTIMIZATIONS  
  void set_dump_SSA_tree(bool f) { dump_SSA_tree = f;}
  void set_dump_SSA_tree_name(const std::string& n)
  {
    ssa_tree_file_name = "__SSA_" + n;
  }
#endif
  
protected:
    void convert_partition(convertort &convertor,
                           interpolating_solvert &interpolator, partitiont &partition);
    void convert_partition_guards(convertort &convertor,
                                  partitiont &partition);

    void convert_partition_assignments(convertort &convertor,
                                       partitiont &partition);

  // Convert a specific partition assumptions of SSA steps
    void convert_partition_assumptions(convertort &convertor,
                                       partitiont &partition);
    // Convert a specific partition assertions of SSA steps
    void convert_partition_assertions(convertort &convertor,
                                      partitiont &partition);
    // Convert a specific partition io of SSA steps
    void convert_partition_io(convertort &convertor,
                              partitiont &partition);
    // Convert a summary partition (i.e., assert its summary)
    void convert_partition_summary(interpolating_solvert &interpolator,
                                   partitiont &partition);

  // Id of the currently selected partition
  partition_idt current_partition_id;

#ifdef DISABLE_OPTIMIZATIONS  
  // FIXME: move to SSA_Reportert class
  bool dump_SSA_tree;
  std::string ssa_tree_file_name;
  
  // For SMT-Lib Translation - Move it later to a new class
  std::map <std::string,exprt>* partition_smt_decl;
  std::stringstream out_terms; // for prints SSA - remove later

  std::stringstream out_basic; // for prints SSA - remove later

  std::stringstream out_partition; // for prints SSA - remove later

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
  void print();
#endif
  unsigned io_count_global; // KE: for Inputs in SSA expression - new CProver version can have more than one input entry

  unsigned count_partition_assertions(const partitiont& partition) const;

  // Safe getter for the current partition
  partitiont& get_current_partition() {
    return partitions[current_partition_id];
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

  virtual void goto_instruction(
    const exprt &guard,
    const exprt &cond,
    //const renamedt<exprt, L2> &cond, //const exprt &cond,
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
