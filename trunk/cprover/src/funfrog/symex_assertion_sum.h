/*******************************************************************
 Module: Symbolic execution and deciding of a given goto-program
 using and generating function summaries. Based on CPROVER goto_symex
 Author: Ondrej Sery, Karine Mendoza, Martin Blicha, Sepideh Asadi
This takes a goto-program and translates it to an equation system by traversing the program.
The output of symbolic execution is a system of equations, asserations and assumptions;
 \*******************************************************************/

#ifndef CPROVER_SYMEX_ASSERTION_SUM_H
#define CPROVER_SYMEX_ASSERTION_SUM_H


#include <util/symbol.h>
#include <goto-symex/goto_symex.h>
#include "partition_fwd.h"
#include <queue>
#include <funfrog/summary_store.h>
#include <iostream>

class goto_programt;
class goto_functionst;
class namespacet;
class assertion_infot;
class call_tree_nodet;
class partitioning_target_equationt;
class partition_ifacet;

using partition_iface_ptrst = std::list<partition_ifacet*>;

class symex_assertion_sumt : public goto_symext
{
public:
/*******************************************************************
Function: symex_assertion_sumt::symex_assertion_sumt

Constructor
/// Construct a goto_symext to execute a particular program
/// \param mh: The message handler to use for log messages
/// \param outer_symbol_table: The symbol table for the program to be
///   executed, excluding any symbols added during the symbolic execution
/// \param _target: Where to store the equation built up by this execution
/// \param options: The options to use to configure this execution
/// \param path_storage: Place to storage symbolic execution paths that have
/// been halted and can be resumed later
/// \param guard_manager: Manager for creating guards

///The state that symbolic execution maintains is not a member anymore.
///Symbolic execution state for current instruction will be pass around
\*******************************************************************/
  symex_assertion_sumt(
    const goto_functionst & _goto_functions,
    call_tree_nodet & _call_info,
    const optionst &_options,
    path_storaget &_path_storage,
    const symbol_tablet & outer_symbol_table,
    partitioning_target_equationt & _target,
    message_handlert & _message_handler,
    const goto_programt & _goto_program,
    unsigned _last_assertion_loc,
    bool _single_assertion_check,
    bool _do_guard_expl,
    unsigned int _max_unwind, bool partial_loops,
    guard_managert & guard_manager);
    
  // MB: to prevent passing arguments in wrong order, since int is implicitly convertible to bool
  symex_assertion_sumt(
  const goto_functionst &, call_tree_nodet &, const optionst &, path_storaget &,
  const symbol_tablet&, partitioning_target_equationt&, message_handlert&,
  const goto_programt&, unsigned int,
  bool, bool, bool, bool) = delete;
          
  virtual ~symex_assertion_sumt() override;

  // Generate SSA statements for the program starting from the root
  // stored in goto_program.
  bool prepare_SSA();
  
  // usage in upgrade check; Generate SSA statements for the subtree
  // of a specific function and compare to its summary
  bool prepare_subtree_SSA();

  // Generate SSA statements for the refined program starting from the given
  // set of functions.
  bool refine_SSA(const std::list<call_tree_nodet *> & refined_function);
  
  /// \brief Called for each step in the symbolic execution
  /// This calls \ref print_symex_step to print symex's current instruction if
  /// required, then \ref execute_next_instruction to execute the actual
  /// instruction body.
  /// \param get_goto_function: The delegate to retrieve function bodies (see
  ///   \ref get_goto_functiont)
  /// \param state: Symbolic execution state for current instruction
  virtual void
  symex_step(const get_goto_functiont &get_goto_function, statet &state) override;

  const partition_iface_ptrst* get_partition_ifaces(const call_tree_nodet * call_tree_node) {
    auto it = partition_iface_map.find(call_tree_node);
    
    if (it == partition_iface_map.end())
      return nullptr;
    return &(it->second);
  };

  partitioning_target_equationt & get_target_equation(){
      return equation;
  }

  std::map<irep_idt, std::string> guard_expln;

  void set_assertion_info_to_verify(const assertion_infot* assertion_info){
      current_assertion = assertion_info;
  }

protected:
  std::unique_ptr<statet> state; //HiFrog specific.

  // Allocated partition interfaces
  partition_iface_ptrst partition_ifaces;

  void end_symex(statet &state);

  // Mapping call_tree_nodes (i.e. call sites in goto program) to partition interfaces
    // Single call_tree_node can map to multiple partitions (e.g. when the call site is inside a loop that is unwound multiple times
  using partition_iface_mapt =  std::unordered_map<const call_tree_nodet*,partition_iface_ptrst>;
  partition_iface_mapt partition_iface_map;

  class deferred_functiont {
  public:

    deferred_functiont(call_tree_nodet &_call_tree_node,
            partition_ifacet& _partition_iface) : call_tree_node(_call_tree_node),
            partition_iface(_partition_iface) { }

    call_tree_nodet& call_tree_node;
    partition_ifacet& partition_iface;
  };

  const goto_functionst& goto_functions;

  // Which functions should be summarized, abstracted from, and which inlined
  call_tree_nodet &call_tree_root;

  // Summary info of the function being currently processed. Set to NULL when
  // no deferred function are left
  call_tree_nodet *current_call_tree_node;

  // Wait queue for the deferred functions (for other partitions)
  std::queue<deferred_functiont> deferred_functions;

  // Store the symex result (The output of symbolic execution is a system of equations)
  //SSA equation
  partitioning_target_equationt &equation;

  // Artificial identifiers for which we do not need Phi function
  std::set<irep_idt> dead_identifiers;

  // refers to Current assertion in process //In symex when there are multiple assertins(all-claims) only one claim at a time is processed
  const assertion_infot* current_assertion {nullptr};

  const goto_programt &goto_program;

  unsigned last_assertion_loc;

  unsigned loc {0};

  bool single_assertion_check;

  bool do_guard_expl;

  // Add function to the wait queue to be processed by symex later and to
  // create a separate partition for interpolation
  void defer_function(const deferred_functiont &deferred_function, bool is_new = true);

  // Are there any more instructions in the current function or at least
  // a deferred function to dequeue?
  bool has_more_steps(const statet &state) {
    return current_call_tree_node != nullptr;
  }
  
  // Processes current code (pointed to by the state member variable) as well
  // as all the deferred functions
  bool process_planned(statet & state);

  // Take a deferred function from the queue and prepare it for symex
  // processing. This would also mark a corresponding partition in
  // the target equation.
  void dequeue_deferred_function(statet &state);

  // The currently processed deferred function
  const deferred_functiont& get_current_deferred_function() const {
    return deferred_functions.front();
  }

  // Processes a function call based on the corresponding
  // summary type
  void handle_function_call(statet &state,
    code_function_callt &function_call);

  // Summarizes the given function call
  void summarize_function_call(
        deferred_functiont& deferred_function,
        statet& state,
        const irep_idt& function_id);
    
  // Prepares a partition with an inverted summary. This is used
  // to verify that a function still implies its summary (in upgrade check).
//  void fill_inverted_summary(call_tree_nodet& summary_info,
//                             statet& state, partition_ifacet& inlined_iface);

  // Inlines the given function call
  void inline_function_call(
        deferred_functiont& deferred_function,
        statet& state,
        const irep_idt& function_id);

  // Abstract from the given function call (nondeterministic assignment to
  // all the possibly modified variables)
  void havoc_function_call(
        deferred_functiont& deferred_function,
        statet& state,
        const irep_idt& function_id);

  // Creates fresh symbols for all the arguments, accessed globals and return
  // value. This is used in upgrade checking to unify symbols of the inverted
  // summary and the function subtree.
  void prepare_fresh_arg_symbols(statet& state,
          partition_ifacet& partition_iface);
  
  // Assigns function arguments to new SSA symbols, also makes
  // assignment of the new SSA symbol of return value to the lhs of
  // the call site (if any)
  void assign_function_arguments(statet & state,
                                 code_function_callt & function_call,
                                 partition_ifacet & partition_iface);
  
  // Marks the SSA symbols of function arguments
  void mark_argument_symbols(const code_typet & function_type, partition_ifacet & partition_iface);

  // Marks the SSA symbols of accessed globals
  void mark_accessed_global_symbols(const irep_idt & function_id, partition_ifacet & partition_iface);

  // Assigns values from the modified global variables. Marks the SSA symbol 
  // of the global variables for later use when processing the deferred function
  void modified_globals_assignment_and_mark(
    const irep_idt &function_id,
    statet &state,
    partition_ifacet &partition_iface);

  // Assigns return value from a new SSA symbols to the lhs at
  // call site. Marks the SSA symbol of the return value temporary
  // variable for later use when processing the deferred function
  void return_assignment_and_mark(
    const code_typet &function_type,
    statet &state,
    const exprt *lhs,
    partition_ifacet &partition_iface,
    bool skip_assignment = false);

  // Assigns modified globals to the corresponding temporary SSA symbols
  void store_modified_globals(
          statet &state,
    const deferred_functiont &deferred_function);

  // Assigns return value to the corresponding temporary SSA symbol
  void store_return_value(
          statet &state,
    const deferred_functiont &deferred_function);

  // Clear local symbols from the l2 cache.
  void clear_locals_versions(statet &state);
  
  // Creates new call site (start & end) symbols for the given
  // deferred function
  void produce_callsite_symbols(partition_ifacet& partition_iface,
                                statet& state);

  // Inserts assumption that a given call ended (i.e., an assumption of
  // the callend symbol)
  void produce_callend_assumption(
        const partition_ifacet& partition_iface, statet& state);

  // Makes an assignment without increasing the version of the
  // lhs symbol (make sure that lhs symbol is not assigned elsewhere)

    void raw_assignment(
            statet &state,
            const ssa_exprt &lhs,
            const symbol_exprt &rhs,
            const namespacet &ns);

  // Adds the given symbol to the current context. If dead, the identifier
  // is only marked as dead (it is not added as a new symbol).
  void add_symbol(const irep_idt& base_id,
                    const typet& type, 
                    bool dead, 
                    bool is_shared, // L0: not in use if shared
                    const source_locationt & source_location) {
    if (dead) {
        dead_identifiers.insert(base_id);
    }  
    
    /* Even if dead adds it, else cannot get L1 name later on */
    if (!get_symbol_table().has_symbol(base_id)) {
        symbolt s;
        s.base_name = base_id;
        s.name = base_id;
        s.type = type;
        s.mode=irep_idt();
        s.location = source_location;
        s.is_thread_local = !is_shared;
        get_symbol_table().add(s);
    }
  }

  // Dead identifiers do not need to be considered in Phi function generation
  bool is_dead_identifier(const irep_idt& identifier) {
    if (identifier == goto_symext::statet::guard_identifier())
      return true;

    return dead_identifiers.find(identifier) != dead_identifiers.end();
  }

  // Allocate new partition_interface
  partition_ifacet& new_partition_iface(call_tree_nodet& call_tree_node,
          partition_idt parent_id, unsigned call_loc);

  const goto_functionst::goto_functiont & get_function(const irep_idt & function_id) const {
      return goto_functions.function_map.at(function_id);
  }

  using globalst = std::vector<irep_idt>;
  // because of recursive functions, we create empty collections if they function is not there yet
  globalst get_modified_globals(irep_idt function_name){
//      return modified_globals.at(function_name);
      return modified_globals[function_name];
  }
  globalst get_accessed_globals(irep_idt function_name) {
//      return accessed_globals.at(function_name);
      return accessed_globals[function_name];
  }
   
protected:
  // KE: override from goto_symex.h
  void phi_function(
    const statet::goto_statet &goto_state,
    statet &state) override;

  // KE: override from goto_symex.h
  void vcc(
    const exprt &expr,
    const std::string &msg,
    statet &state) override;

  // for loop unwinding
  virtual bool get_unwind(
    const symex_targett::sourcet &source,
    const call_stackt &call_stack, // KE: changed to fit the override
    unsigned unwind)
  {
    // returns true if we should not continue unwinding
    // for support of different bounds in different loops, see how it's done in symex_bmct
    return unwind >= max_unwind;
  }

  // unwind option
  unsigned int max_unwind;

  /* Temporary fix to deal with loops
   * taken from void goto_symext::symex_goto(statet &state)
   * in symex_goto.cpp
   */
  bool is_unwind_loop(statet &state);
  unsigned int prev_unwind_counter {0}; // Updated on branching: Goto, Funcation_Call and End_Function
  
  #ifdef DEBUG_PARTITIONING
    std::set<std::string> _return_vals; // Check for duplicated symbol creation
  #endif

/// The symbol table associated with the goto-program that we're
  /// executing. This symbol table will not additionally contain objects
  /// that are dynamically created as part of symbolic execution; the
  /// names of those object are stored in the symbol table passed as the
  /// `symex_symbol_table` argument to the `symex_*` methods.
  // const symbol_tablet &outer_symbol_table; <--- this is a const method in goto_symex.h
//  symbol_tablet* symex_symbol_table;  // We use this to all our dynamic allocations! (as done in bmc.h

    symbol_tablet& get_symbol_table() { return state->symbol_table; }
    const symbol_tablet& get_symbol_table() const { return state->symbol_table; }

private:

    std::unordered_map<irep_idt, globalst, irep_id_hash> accessed_globals;  //SA?: Globals accessed (read, modified? or both) in the function
    std::unordered_map<irep_idt, globalst, irep_id_hash> modified_globals;  // Globals modified in the function

    // Intended to let the state know about symbols that are not declared anywhere, like extern variables
    void add_globals_to_state(statet & state);

    void analyze_globals();

    void analyze_globals_rec(irep_idt function_to_analyze, std::unordered_set<irep_idt, irep_id_hash> & analyzed_functions);

  // Methods for manipulating symbols: creating new artifical symbols, getting the current L2 version of a symbol,
  // getting the next version of a symbol, etc.

  // this should be used only for artificial symbols that we have created with create_new_artificial_symbol method
  bool knows_artificial_symbol(const irep_idt & symbol_id) const {
    return get_symbol_table().has_symbol(symbol_id);
  }

  // this should be used only for symbols that we have created with create_new_artificial_symbol method
  const symbolt & get_artificial_symbol(const irep_idt & id){
    const symbolt * symbol_p = get_symbol_table().lookup(id);
    if(symbol_p){
      return *symbol_p;
    }
    throw std::logic_error(std::string("Symbol for identifier ") + id.c_str() + " was not found!");
  }

  const symbolt & get_normal_symbol(const irep_idt & id) const {
    return ns.lookup(id);
  }

  void create_new_artificial_symbol(const irep_idt & id, const typet & type, bool is_dead);

  // NOTE: use only when versions for interface symbols are needed!
  ssa_exprt get_current_version(const symbolt & symbol);
    
// Note from CPROVER 5.12 about const propagation:
// We cannot remove the object from the L1 renaming map, because L1 renaming
// information is not local to a path, but removing it from the propagation
// map and value-set is safe as 1) it is local to a path and 2) this
// instance can no longer appear.
// Remove from the local L2 renaming map; this means any reads from the dead
// identifier will use generation 0 (e.g. x!N@M#0, where N and M are
// positive integers), which is never defined by any write, and will be
// dropped by `goto_symext::merge_goto` on merging with branches where the
// identifier is still live.
  void  stop_constant_propagation_for(const irep_idt & id) {
    //state.propagation.remove(id);
    state->propagation.erase_if_exists(id);
  }

  // this works only for identifiers of artificial symbols
  ssa_exprt get_next_version(const irep_idt& id) {
    assert(knows_artificial_symbol(id));
    return get_next_version(get_artificial_symbol(id));
  }

  // NOTE: use only for interface symbols! (symbols at methods' interface)
  // increments the L2 counter in the process
  ssa_exprt get_next_version(const symbolt & symbol);

  // Get L1 version of a symbol
  ssa_exprt get_l1_ssa(const symbolt & symbol) {
    ssa_exprt ssa(symbol.symbol_expr());
    auto res = state->rename_ssa<L1>(ssa, ns).get();
    return res;
  }

  dstringt get_l1_identifier(const symbolt & symbol) {
    return get_l1_ssa(symbol).get_l1_object_identifier();
  }

  symbolt get_tmp_ret_val_symbol(const partition_ifacet& iface);

  // to be able to start with a fresh state
  void reset_state(){
  auto* storage = &this->path_storage;
  // Clear the state
  state = std::unique_ptr<statet>(new statet(
	  symex_targett::sourcet(goto_functions.entry_point(), goto_program),
	  symex_config.max_field_sensitivity_array_size,
	  guard_manager,
	  [storage](const irep_idt &id) { return storage->get_unique_l2_index(id); }));
	ns = namespacet{outer_symbol_table, state->symbol_table};
	// since not supporting multiple threads, we do not need to record events;
	turn_off_recording_events();
  }

  void turn_off_recording_events() {
  	// turns off doing some book-keeping related to handling multiple threads by CProver
	state->record_events.push(false);
  }
    /// Assuming the program counter of \p state is currently pointing to a return
    /// instruction, assign the value in that return to the top frame's
    /// \p return_value field.
    void return_assignment(statet &);
};
#endif
