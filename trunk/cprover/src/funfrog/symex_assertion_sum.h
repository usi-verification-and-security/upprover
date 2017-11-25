/*******************************************************************
 Module: Symbolic execution and deciding of a given goto-program
 using and generating function summaries. Based on symex_asserion.h.

 Author: Ondrej Sery

 \*******************************************************************/

#ifndef CPROVER_SYMEX_ASSERTION_SUM_H
#define CPROVER_SYMEX_ASSERTION_SUM_H

#include <queue>

#include <cbmc/symex_bmc.h>
#include <util/symbol.h>
#include <util/ui_message.h>

#include "partition_iface_fwd.h"
#include "partitioning_target_equation.h"

//#define DEBUG_PARTITIONING // Debug this class

class goto_programt;
class goto_functionst;
class goto_symex_statet;
class namespacet;
class assertion_infot;
class summary_infot;
class summarization_contextt;

class symex_assertion_sumt : public symex_bmct
{
public:
  symex_assertion_sumt(
          summarization_contextt &_summarization_context,
          summary_infot &_summary_info,
          const namespacet &_ns,
          symbol_tablet &_new_symbol_table,
          partitioning_target_equationt &_target,
          ui_message_handlert &_message_handler,
          const goto_programt &_goto_program,
          unsigned _last_assertion_loc,
          bool _single_assertion_check,
          bool _use_slicing=true,
	  bool _do_guard_expl=true,
          bool _use_smt=true
          ) :
          symex_bmct(_ns, _new_symbol_table, _target),
          summarization_context(_summarization_context),
          summary_info(_summary_info),
          current_summary_info(&_summary_info),
          equation(_target),
          current_assertion(NULL),
          message_handler(_message_handler),
          goto_program(_goto_program),
          last_assertion_loc(_last_assertion_loc),
          loc(0),
          single_assertion_check(_single_assertion_check),
          use_slicing(_use_slicing),
	  do_guard_expl(_do_guard_expl),
          use_smt(_use_smt),
          prev_unwind_counter(0)
          {set_message_handler(_message_handler);}
          
  virtual ~symex_assertion_sumt();

  void loop_free_check();

  // Generate SSA statements for the program starting from the root 
  // stored in goto_program.
  bool prepare_SSA(const assertion_infot &assertion);

  // Generate SSA statements for the subtree of a specific function and
  // compare to its summary
  bool prepare_subtree_SSA(const assertion_infot &assertion);

  // Generate SSA statements for the refined program starting from the given 
  // set of functions.
  bool refine_SSA(
          const std::list<summary_infot*> &refined_function,
          bool force_check = false);
  
  virtual void symex_step(
    const goto_functionst &goto_functions,
    goto_symex_statet &state);
  
  const partition_iface_ptrst* get_partition_ifaces(summary_infot &summary_info) { 
    partition_iface_mapt::iterator it = partition_iface_map.find(&summary_info);
    
    if (it == partition_iface_map.end())
      return NULL;
    return &(it->second);
  };

  std::map<irep_idt, std::string> guard_expln;

  // Shall be public for refinement
  void fabricate_cprover_SSA(irep_idt base_symbol_id, 
        const typet& type, const source_locationt source_location, 
        bool is_rename, bool is_dead, ssa_exprt& ret_symbol);
  
private:
  
  // Symex state holding the renaming levels
  goto_symex_statet state;
  // Allocated partition interfaces
  partition_iface_ptrst partition_ifaces;

  void end_symex(goto_symex_statet &state);

  // Mapping from summary_info to the corresponding partition_iface
  typedef std::unordered_map<const summary_infot*,partition_iface_ptrst> partition_iface_mapt;
  partition_iface_mapt partition_iface_map;

  class deferred_functiont {
  public:

    deferred_functiont(summary_infot &_summary_info,
            partition_ifacet& _partition_iface) : summary_info(_summary_info),
            partition_iface(_partition_iface) { }

    summary_infot& summary_info;
    partition_ifacet& partition_iface;
  };

  // Shared information about the program and summaries to be used during
  // analysis
  summarization_contextt &summarization_context;

  // Which functions should be summarized, abstracted from, and which inlined
  summary_infot &summary_info;

  // Summary info of the function being currently processed. Set to NULL when
  // no deferred function are left
  summary_infot *current_summary_info;

  // Wait queue for the deferred functions (for other partitions)
  std::queue<deferred_functiont> deferred_functions;

  // Store for the symex result
  partitioning_target_equationt &equation;

  // Artificial identifiers for which we do not need Phi function
  std::set<irep_idt> dead_identifiers;

  // Current assertion
  const assertion_infot* current_assertion;

  //std::ostream &out;
  ui_message_handlert &message_handler;

  const goto_programt &goto_program;

  unsigned last_assertion_loc;

  unsigned loc;

  bool single_assertion_check;

  bool use_slicing;

  bool do_guard_expl;
  
  bool use_smt; // for slicing 
  
  // Add function to the wait queue to be processed by symex later and to
  // create a separate partition for interpolation
  void defer_function(const deferred_functiont &deferred_function);

  // Are there any more instructions in the current function or at least
  // a deferred function to dequeue?
  bool has_more_steps(const goto_symex_statet &state) {
    return current_summary_info != NULL;
  }
  
  // Processes current code (pointed to by the state member variable) as well
  // as all the deferred functions
  bool process_planned(goto_symex_statet &state, bool force_check = false);

  // Take a deferred function from the queue and prepare it for symex
  // processing. This would also mark a corresponding partition in
  // the target equation.
  void dequeue_deferred_function(goto_symex_statet &state);

  // The currently processed deferred function
  const deferred_functiont& get_current_deferred_function() const {
    return deferred_functions.front();
  }

  // Processes a function call based on the corresponding
  // summary type
  void handle_function_call(goto_symex_statet &state,
    code_function_callt &function_call);

  // Summarizes the given function call
  void summarize_function_call(
        deferred_functiont& deferred_function,
        goto_symex_statet& state,
        const irep_idt& function_id);
    
  // Prepares a partition with an inverted summary. This is used
  // to verify that a function still implies its summary (in upgrade check).
  void fill_inverted_summary(summary_infot& summary_info,
                             goto_symex_statet& state, partition_ifacet& inlined_iface);

  // Inlines the given function call
  void inline_function_call(
        deferred_functiont& deferred_function,
        goto_symex_statet& state,
        const irep_idt& function_id);

  // Abstract from the given function call (nondeterministic assignment to
  // all the possibly modified variables)
  void havoc_function_call(
        deferred_functiont& deferred_function,
        goto_symex_statet& state,
        const irep_idt& function_id);

  // Creates fresh symbols for all the arguments, accessed globals and return
  // value. This is used in upgrade checking to unify symbols of the inverted
  // summary and the function subtree.
  void prepare_fresh_arg_symbols(goto_symex_statet& state,
          partition_ifacet& partition_iface);
  
  // Assigns function arguments to new SSA symbols, also makes
  // assignment of the new SSA symbol of return value to the lhs of
  // the call site (if any)
  void assign_function_arguments(goto_symex_statet &state,
    code_function_callt &function_call,
    deferred_functiont &deferred_function);
  
  // Marks the SSA symbols of function arguments
  void mark_argument_symbols(
    const code_typet &function_type,
    goto_symex_statet &state,
    partition_ifacet &partition_iface);

  // Marks the SSA symbols of accessed globals
  void mark_accessed_global_symbols(
    const irep_idt &function_id,
    goto_symex_statet &state,
    partition_ifacet &partition_iface,
    bool is_init_stage);

  // L2 rename - new code
  void level2_rename_init(goto_symex_statet &state, const symbol_exprt &expr);

  // Assigns values from the modified global variables. Marks the SSA symbol 
  // of the global variables for later use when processing the deferred function
  void modified_globals_assignment_and_mark(
    const irep_idt &function_id,
    goto_symex_statet &state,
    partition_ifacet &partition_iface);

  // Assigns return value from a new SSA symbols to the lhs at
  // call site. Marks the SSA symbol of the return value temporary
  // variable for later use when processing the deferred function
  void return_assignment_and_mark(
    const code_typet &function_type,
    goto_symex_statet &state,
    const exprt *lhs,
    partition_ifacet &partition_iface,
    bool skip_assignment = false);

  // Assigns modified globals to the corresponding temporary SSA symbols
  void store_modified_globals(
          goto_symex_statet &state,
    const deferred_functiont &deferred_function);

  // Assigns return value to the corresponding temporary SSA symbol
  void store_return_value(
          goto_symex_statet &state,
    const deferred_functiont &deferred_function);

  // Clear local symbols from the l2 cache.
  void clear_locals_versions(goto_symex_statet &state);
  
  // Creates new call site (start & end) symbols for the given
  // deferred function
  void produce_callsite_symbols(partition_ifacet& partition_iface,
                                goto_symex_statet& state);

  // Inserts assumption that a given call ended (i.e., an assumption of
  // the callend symbol)
  void produce_callend_assumption(
        const partition_ifacet& partition_iface, goto_symex_statet& state);

  // Helper function for renaming of an identifier without
  // assigning to it. Constant propagation is stopped for the given symbol.
  irep_idt get_new_symbol_version(
        const irep_idt& identifier,
        goto_symex_statet &state,
        typet type);

  // Replace old interface of get current name from counter
  irep_idt get_current_l2_name(goto_symex_statet &state, const irep_idt &identifier) const;

  // Makes an assignment without increasing the version of the
  // lhs symbol (make sure that lhs symbol is not assigned elsewhere)
  void raw_assignment(goto_symex_statet &state,
        exprt &lhs,
        const exprt &rhs,
        const namespacet &ns); 
        //bool record_value); //Always false, removed


  // Adds the given symbol to the current context. If dead, the identifier
  // is only marked as dead (it is not added as a new symbol).
  void add_symbol(const irep_idt& base_id,
                    const typet& type, 
                    bool dead, 
                    bool is_shared, // L0: not in use if shared
                    const source_locationt source_location) {
    if (dead) {
        dead_identifiers.insert(base_id);
    }  
    
    /* Even if dead adds it, else cannot get L1 name later on */
    if (!new_symbol_table.has_symbol(base_id)) {
        symbolt s;
        s.base_name = base_id;
        s.name = base_id;
        s.type = type;
        s.mode=irep_idt();
        s.location = source_location;
        s.is_thread_local = !is_shared;
        new_symbol_table.add(s);
    }
  }

  // Dead identifiers do not need to be considered in Phi function generation
  bool is_dead_identifier(const irep_idt& identifier) {
    if (identifier == guard_identifier)
      return true;

    return dead_identifiers.find(identifier) != dead_identifiers.end();
  }

  // Allocate new partition_interface
  partition_ifacet& new_partition_iface(summary_infot& summary_info,
          partition_idt parent_id, unsigned call_loc);
   
protected:
  // KE: override from goto_symex.h
  virtual void phi_function(
    const goto_symex_statet::goto_statet &goto_state,
    goto_symex_statet &state) override;

  // KE: override from goto_symex.h
  virtual void vcc(
    const exprt &vcc_expr,
    const std::string &msg,
    goto_symex_statet &state) override;
  
  /* Temporary fix to deal with loops
   * taken from void goto_symext::symex_goto(statet &state)
   * in symex_goto.cpp
   */
  bool is_unwind_loop(goto_symex_statet &state);
  unsigned int prev_unwind_counter; // Updated on branching: Goto, Funcation_Call and End_Function
  
  #ifdef DEBUG_PARTITIONING
    std::set<std::string> _return_vals; // Check for duplicated symbol creation
  #endif
};
#endif
