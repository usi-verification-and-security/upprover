/*******************************************************************

 Module: Symbolic execution and deciding of a given goto-program
 using and generating function summaries. Based on symex_asserion.cpp

 Author: Ondrej Sery

\*******************************************************************/

#include "symex_assertion_sum.h"


#include <util/expr_util.h>
#include <goto-symex/goto_symex.h>
#include <pointer-analysis/add_failed_symbols.h>
#include <util/time_stopping.h>
#include <util/base_type.h>

#include "partitioning_slice.h"
#include "partition_iface.h"
#include "utils/naming_helpers.h"
#include "partitioning_target_equation.h"
#include "hifrog.h"
#include "summary_store.h"
#include "assertion_info.h"

#include <memory>
#include <algorithm>
#include <iostream>

#ifdef DEBUG_SSA
#include "utils/ssa_helpers.h"
#endif // DEBUG_SSA

/*******************************************************************

 Function: symex_assertion_sumt::symex_assertion_sumt

 Constructor

\*******************************************************************/
symex_assertion_sumt::symex_assertion_sumt(
  const summary_storet & _summary_store,
  const goto_functionst & _goto_functions,
  call_tree_nodet &_root,
  const namespacet &_ns,
  symbol_tablet &_new_symbol_table,
  partitioning_target_equationt &_target,
  message_handlert &_message_handler,
  const goto_programt &_goto_program,
  unsigned _last_assertion_loc,
  bool _single_assertion_check,
  bool _use_slicing,
  bool _do_guard_expl,
  bool _use_smt,
  unsigned int _max_unwind,
  bool partial_loops
) :
  goto_symext(_message_handler, _ns, _new_symbol_table, _target),
  summary_store(_summary_store),
  goto_functions(_goto_functions),
  call_tree_root(_root),
  current_call_tree_node(&_root),
  equation(_target),
  goto_program(_goto_program),
  last_assertion_loc(_last_assertion_loc),
  single_assertion_check(_single_assertion_check),
  use_slicing(_use_slicing),
  do_guard_expl(_do_guard_expl),
  use_smt(_use_smt),
  max_unwind(_max_unwind)
{
  options.set_option("partial-loops", partial_loops);
  analyze_globals();
}

/*******************************************************************

 Function: symex_assertion_sumt::~symex_assertion_sumt

 Inputs:

 Outputs:

 Purpose: Delete all allocated partition_ifaces

\*******************************************************************/

symex_assertion_sumt::~symex_assertion_sumt() {
  for (auto iface : partition_ifaces){
    delete iface;
  }
}

/*******************************************************************

 Function: symex_assertion_sumt::loop_free_check

 Inputs:

 Outputs:

 Purpose: Sanity check, we expect loop-free programs only.
 * 
 * KE: DEAD CODE

 * KE: not compiling, comment + assert(0);

\*******************************************************************/

void symex_assertion_sumt::loop_free_check(){
# ifndef NDEBUG
  assert(0); // Dead code
/*
  forall_goto_program_instructions(it, goto_program)
    assert(!it->is_backwards_goto());
  forall_goto_functions(it, summarization_context.get_functions()) {
    forall_goto_program_instructions(it2, it->second.body) {
      if (it2->is_backwards_goto()) {
        std::cerr << "ERROR: Backward goto (i.e., a loop) in function: " << it->first << std::endl;
        goto_program.output_instruction(ns, "", std::cout, it2);
        // assert(!it2->is_backwards_goto());
      }
    }
  }
*/
# endif
}

/*******************************************************************

 Function: symex_assertion_sumt::prepare_SSA

 Inputs:

 Outputs:

 Purpose: Generate SSA statements for the program starting from the root 
 stored in goto_program.

\*******************************************************************/

bool symex_assertion_sumt::prepare_SSA(const assertion_infot &assertion)
{
  current_assertion = &assertion;

  // these are quick...
  if(assertion.is_trivially_true())
  {
    log.statistics() << "ASSERTION IS TRUE" << log.eom;
    return true;
  }

  // Clear the state
  reset_state();
  add_globals_to_state(state);

  // Prepare the partitions and deferred functions
  partition_ifacet &partition_iface = new_partition_iface(call_tree_root, NO_PARTITION_ID, 0);
  defer_function(deferred_functiont(call_tree_root, partition_iface));
  equation.select_partition(partition_iface.partition_id);

  // Old: ??? state.value_set = value_sets;
  state.source.pc = goto_program.instructions.begin();
  
  loc = 0;
  return process_planned(state);
}

/*******************************************************************

 Function: symex_assertion_sumt::prepare_subtree_SSA

 Inputs:

 Outputs:

 Purpose: Generate SSA statements for the subtree of a specific function and
 compare to its summary

\*******************************************************************/

//bool symex_assertion_sumt::prepare_subtree_SSA(const assertion_infot &assertion)
//{
//  current_assertion = &assertion;
//
//  // Clear the state
//  reset_state();
//
//  // Prepare a partition for the ROOT function and defer
//  partition_ifacet &partition_iface = new_partition_iface(call_tree_root, partitiont::NO_PARTITION, 0);
//  call_tree_root.set_inline();
//  defer_function(deferred_functiont(call_tree_root, partition_iface));
//
//  // Make all the interface symbols shared between
//  // the inverted summary and the function.
//  prepare_fresh_arg_symbols(state, partition_iface);
//
//  // Prepare a partition for the inverted SUMMARY
//  fill_inverted_summary(call_tree_root, state, partition_iface);
//
//  // Old: ??? state.value_set = value_sets;
//  state.source.pc = get_function(partition_iface.function_id).body.instructions.begin();
//
//  // Plan the function for processing
//  dequeue_deferred_function(state);
//
//  return process_planned(state, true);
//}

/*******************************************************************

 Function: symex_assertion_sumt::refine_SSA

 Inputs:

 Outputs:

 Purpose: Generate SSA statements for the refined program starting from 
 the given set of functions.

\*******************************************************************/

bool symex_assertion_sumt::refine_SSA( 
        const std::list<call_tree_nodet*> &refined_functions, bool force_check)
{
  // Defer the functions
  for (const auto & refined_function : refined_functions)
  {
      assert(!refined_function->is_root());
      const partition_iface_ptrst* partition_ifaces = get_partition_ifaces(refined_function);

    if (!refined_function->is_root()) {
        if (partition_ifaces) {
            for(const auto & partition_iface : *partition_ifaces) {
                if (partition_iface->partition_id != NO_PARTITION_ID) {
                    const auto & partition = equation.get_partitions()[partition_iface->partition_id];
                    assert(partition.has_abstract_representation());
                    std::cerr << "Refining partition: " << partition_iface->partition_id << '\n';
                    //equation.invalidate_partition(partition_iface->partition_id);
                    equation.refine_partition(partition_iface->partition_id);
                }
                auto const & partition = equation.get_partitions()[partition_iface->partition_id];
                if (!partition.has_ssa_representation()) {
                    defer_function(deferred_functiont(*refined_function, *partition_iface), false);
                }
            }
        } else {
          std::cerr << "WARNING: Invalid call to refine_SSA <- " << 
                  "refining previously unseen call \"" << 
                  refined_function->get_function_id().c_str() << "\" (skipped)" << std::endl;
        }
    }
  }
  
  // Plan the function for processing
  dequeue_deferred_function(state);
  
  return process_planned(state, force_check);
}

/*******************************************************************\

Function: symex_assertion_sumt::process_planned

  Inputs:

 Outputs:

 Purpose: Processes current code (pointed to by the state member variable) 
 as well as all the deferred functions

\*******************************************************************/
 
bool symex_assertion_sumt::process_planned(statet &state, bool force_check)
{
  // Proceed with symbolic execution
  absolute_timet before, after;
  before=current_time();

  while (has_more_steps(state))
  {
    symex_step(goto_functions, state);
  }
  after=current_time();

  log.statistics() << "SYMEX TIME: " << (after-before) << log.eom;

  if(remaining_vccs!=0 || force_check)
  {
    if (use_slicing) {
      before=current_time();
      log.statistics() << "All SSA steps: " << equation.SSA_steps.size() << log.eom;
      partitioning_slice(equation, summary_store, use_smt);
      log.statistics() << "Ignored SSA steps after slice: " << equation.count_ignored_SSA_steps() << log.eom;
      after=current_time();
      log.statistics() << "SLICER TIME: " << (after-before) << log.eom;
    }
  } else {
    log.statistics() << "Assertion(s) hold trivially." << log.eom;
    return true;
  }
  return false;
}

/*******************************************************************\

Function: symex_assertion_sumt::symex_step

  Inputs:

 Outputs:

 Purpose: Perform a single symex step. The implementation is based 
 on the goto_symex, but it handles function calls differently. 
 Creation of expressions representing the calls is postponed, so that
 the formulas representing the function bodies can be passed to 
 an interpolating solver as separate conjuncts.i


Note: when upgrading Cprover, please also update the case-switch here
follwoing the changes in symex_main.cpp

\*******************************************************************/

void symex_assertion_sumt::symex_step(
  const goto_functionst &goto_functions,
  statet &state)
{
#ifdef DEBUG_PARTITIONING    
  std::cout << "\ninstruction type is " << state.source.pc->type << '\n';
  std::cout << "Location: " << state.source.pc->source_location << '\n';
  if (state.source.pc->type != DEAD)
  {
    std::cout << "Guard: " << from_expr(ns, "", state.guard.as_expr()) << '\n';
    std::cout << "Code: " << from_expr(ns, "", state.source.pc->code) << '\n';
    std::cout << "Unwind: " << state.top().loop_iterations[goto_programt::loop_id(*state.source.pc)].count << '\n';
    std::cout << "Unwind Info."
              << " unwind in last goto was " << prev_unwind_counter 
              << " a function " << (state.top().loop_iterations.empty() ? "with no" : "with") << " loops"
              << " and is now" << ((is_unwind_loop(state) ? " in loop " : " out of any loop")) << '\n';
  }
#endif

  const goto_programt::instructiont & instruction = *state.source.pc;
  loc++;
  merge_gotos(state);

//  MB: We do not use depth option
//////////////////////////////////  CBMC_CODE
//  // depth exceeded?
//  unsigned max_depth=atoi(options.get_option("depth").c_str());
//  if(max_depth!=0 && state.depth>max_depth)
//      state.guard.add(false_exprt());
//  state.depth++;
//////////////////////////////////  end of CMBC_CODE

  // KE: This switch-case is taken from: Function: goto_symext::symex_step
  switch(instruction.type)
  {
  case SKIP:
    if(!state.guard.is_false())
      target.location(state.guard.as_expr(), state.source);
    symex_transition(state);
    break;

  case END_FUNCTION:

    //decrement_unwinding_counter(); 
    store_return_value(state, get_current_deferred_function());
    end_symex(state);
    prev_unwind_counter = state.top().loop_iterations[goto_programt::loop_id(*state.source.pc)].count;
    break;
  
  case LOCATION:
    if(!state.guard.is_false())
      target.location(state.guard.as_expr(), state.source);
    symex_transition(state);
    break;
  
  case GOTO:
    if (do_guard_expl)
    {
        bool store_expln;
        std::string str;

        store_expln = state.source.pc->guard.has_operands();
        if (store_expln) {
            try { str = from_expr(state.source.pc->guard.op0()); }
            catch (const std::string &s) { str = ""; }
        }
      
        prev_unwind_counter = state.top().loop_iterations[goto_programt::loop_id(*state.source.pc)].count;
        symex_goto(state); // Original code from Cprover follow with break

        if (do_guard_expl &&store_expln && !str.empty())
        {
            guard_expln[state.guard.as_expr().get("identifier")] = str;
        }
    } else {
        prev_unwind_counter = state.top().loop_iterations[goto_programt::loop_id(*state.source.pc)].count;
        symex_goto(state); // Original code from Cprover follow with break
    }
        
    break;
    
  case ASSUME:
    if(!state.guard.is_false())
    {
      exprt tmp = instruction.guard;
      clean_expr(tmp, state, false);
      state.rename(tmp, ns);
      symex_assume(state, tmp);
    }

    symex_transition(state);
    break;

  case ASSERT:
    if(!state.guard.is_false())
    {
      if (get_current_deferred_function().call_tree_node.is_assertion_enabled(state.source.pc)) {
          
        // Skip asserts that are not currently being checked
        if (current_assertion->assertion_matches(state.depth, state.source.pc))
        {
            /* This is the code from ASSERT originally */
            std::string msg=id2string(state.source.pc->source_location.get_comment());
            if(msg.empty()) {
              msg = "assertion";
            }

            exprt tmp(instruction.guard);
            clean_expr(tmp, state, false);
            vcc(tmp, msg, state);
            /* END: This is the code from ASSERT originally */

            // Checks which assert it is, and if we end the loop here
            #ifdef DEBUG_PARTITIONING
                bool is_exit = 
                 ((single_assertion_check  
                    && (!is_unwind_loop(state))
                    && (!get_current_deferred_function().call_tree_node.is_in_loop()))
                  || (loc >= last_assertion_loc && (max_unwind == 1)));
                
                std::cout << "Parsing Assert: " <<
                "\n  file " << state.source.pc->source_location.get_file() <<
                " line " << state.source.pc->source_location.get_line() <<
                " function " << state.source.pc->source_location.get_function() << 
                "\n  " << ((state.source.pc->is_assert()) ? "assertion" : "code") <<
                "\n  " << from_expr(ns, "", state.source.pc->guard) <<
                "\n  " << (is_exit ? "End before in location :" : "Current location ") 
                       << loc << " (out of " << last_assertion_loc << ")" 
                       << " is in loop? " << state.source.pc->loop_number // Check when this will become active
                       << std::endl;
            #endif 
                    
            /* Optimization to remove code that after the current checked assert + remove any other asserts */
            // KE: change later (when supported) to state.source.pc->loop_number
            // KE: Use get_current_unwind(state), if greater than 0 it is inside a loop
            if ((single_assertion_check  
                    && (!is_unwind_loop(state))
                    && (!get_current_deferred_function().call_tree_node.is_in_loop()))
               || (loc >= last_assertion_loc && (max_unwind == 1))) // unwind exactly 1, see line 37 unwind.h to understand why
            {  
              end_symex(state);
              return;
            }
        }
      }
    }

    symex_transition(state);
    break;
    
  case RETURN:
    if(!state.guard.is_false())
    { 
      return_assignment(state);
    }
    
    symex_transition(state);
    break;

  case ASSIGN:      
    if(!state.guard.is_false()) 
      symex_assign_rec(state, to_code_assign(instruction.code));
          
    symex_transition(state);
    break;

  case FUNCTION_CALL:
    if(!state.guard.is_false())
    {  
      code_function_callt deref_code=
        to_code_function_call(instruction.code);
      // Process the function call according to the call_summary
      handle_function_call(state, deref_code);
    }  
    prev_unwind_counter = state.top().loop_iterations[goto_programt::loop_id(*state.source.pc)].count;
    symex_transition(state);
    break;

  case OTHER:
    if(!state.guard.is_false())
      symex_other(goto_functions, state);

    symex_transition(state);
    break;

  case DECL:
    if(!state.guard.is_false())
      symex_decl(state);

    symex_transition(state);
    break;

  case DEAD:
    // ignore for now
    symex_transition(state);
    break;

  case START_THREAD:
    throw "START_THREAD not yet implemented";
    
  case END_THREAD:
    {
      // behaves like assume(0);
      state.guard.add(false_exprt());
      exprt tmp=state.guard.as_expr();
      target.assumption(state.guard.as_expr(), tmp, state.source);
    }
    symex_transition(state);
    break;
  
  case ATOMIC_BEGIN:
  case ATOMIC_END:
    // these don't have path semantics
    symex_transition(state);
    break;
  
  default:
    assert(false);
  }
}

/*******************************************************************

 Function: symex_assertion_sumt::defer_function

 Inputs:

 Outputs:

 Purpose: Add function to the wait queue to be processed by symex later and to
 create a separate partition for interpolation.

\*******************************************************************/
void symex_assertion_sumt::defer_function(
        const deferred_functiont &deferred_function,
        bool is_new)
{
  deferred_functions.push(deferred_function);
  if(is_new){
      equation.reserve_partition(deferred_function.partition_iface);
  }
}

/*******************************************************************

 Function: symex_assertion_sumt::dequeue_deferred_function

 Inputs:

 Outputs:

 Purpose: Take a deferred function from the queue and prepare it for 
 symex processing. This would also mark a corresponding partition in
 the target equation.

\*******************************************************************/
void symex_assertion_sumt::dequeue_deferred_function(statet& state)
{
  if (deferred_functions.empty()) {
    // No more deferred functions, we are done
    current_call_tree_node = nullptr;
    // Prepare the equation for further processing
    equation.prepare_partitions();
   
/*#   ifdef DEBUG_PARTITIONING    
    std::cerr << std::endl << "Current names L2 (" << 
            state.level2.current_names.size() << "):" << std::endl;
    for (statet::level2t::current_namest::const_iterator it =
            state.level2.current_names.begin();
            it != state.level2.current_names.end();
            ++it) {
      std::cerr << it->first.c_str() << " : " << it->second.count << std::endl;
    }
    std::cerr << std::endl << "Current names L1 (" << 
            state.top().level1.current_names.size() << "):" << std::endl;
    for (statet::level1t::current_namest::const_iterator it =
            state.top().level1.current_names.begin();
            it != state.top().level1.current_names.end();
            ++it) {
      std::cerr << it->first.c_str() << " : " << it->second << std::endl;
    }
    std::cerr << std::endl;
#   endif*/
    return;
  }

  // Set the current summary info to one of the deferred functions
  deferred_functiont &deferred_function = deferred_functions.front();
  partition_ifacet &partition_iface = deferred_function.partition_iface;
  current_call_tree_node = &deferred_function.call_tree_node;
  const irep_idt& function_id = current_call_tree_node->get_function_id();
  loc = current_call_tree_node->get_call_location();

  log.statistics () <<  (std::string("Processing a deferred function: ") + function_id.c_str()) << log.eom;

  // Select symex target equation to produce formulas into the corresponding
  // partition
  equation.select_partition(deferred_function.partition_iface.partition_id);

  // Prepare (and empty) the current state
  state.guard.make_true();

  // Set pc to function entry point
  // NOTE: Here, we expect having the function body available
  const goto_functionst::goto_functiont& function = get_function(function_id);
  const goto_programt& body = function.body;
  state.source.pc = body.instructions.begin();
  state.top().end_of_function = --body.instructions.end();
  state.top().goto_state_map.clear();
  state.top().local_objects.clear();

  // Setup temporary store for return value
  if (partition_iface.returns_value) {
    state.top().return_value = get_tmp_ret_val_symbol(partition_iface).symbol_expr();
  } else {
    state.top().return_value.make_nil();
  }

  // Add an assumption of the function call_site symbol
  target.assumption(state.guard.as_expr(), partition_iface.callstart_symbol,
          state.source);

  // NOTE: In order to prevent name clashes with argument SSA versions,
  // we renew them all here.
  for (std::vector<symbol_exprt>::const_iterator it1 =
          partition_iface.argument_symbols.begin();
          it1 != partition_iface.argument_symbols.end();
          ++it1) {
    // KE: Original and first try are commented out
    //symbol_exprt lhs(state.get_original_name(it1->get_identifier()), ns.follow(it1->type()));
    //symbol_exprt lhs = to_symbol_expr(to_ssa_expr(*it1).get_original_expr());
    ssa_exprt lhs(symbol_exprt((to_ssa_expr(*it1).get_original_expr()).get(ID_identifier), ns.follow(it1->type())));
    //FIXME: unify rename/SSA fabrication
    
    // Check before getting into symex_assign_symbol that lhs is correct
    assert(lhs.id()==ID_symbol &&
       lhs.get_bool(ID_C_SSA_symbol) &&
       !lhs.has_operands());
      
    guardt guard;
    // MB without multithreading, no need to record events
    //state.record_events=false;
    assert(state.record_events == false);
    symex_assign_symbol(state, lhs, nil_exprt(), *it1, guard, symex_targett::assignment_typet::HIDDEN);
  }
}

/*******************************************************************

 Function: symex_assertion_sumt::prepare_fresh_arg_symbols

 Inputs:

 Outputs:

 Purpose: Creates fresh symbols for all the arguments, accessed globals 
 and return value. This is used in upgrade checking to unify symbols 
 of the inverted summary and the function subtree.

\*******************************************************************/

void symex_assertion_sumt::prepare_fresh_arg_symbols(statet& state,
        partition_ifacet& partition_iface)
{
  const irep_idt &identifier = partition_iface.function_id;

  // find code in function map
  const goto_functionst::goto_functiont &goto_function = get_function(identifier);

  // Callsite symbols
  produce_callsite_symbols(partition_iface, state);

  // Store the argument renamed symbols somewhere (so that we can use
  // them later, when processing the deferred function).
  mark_argument_symbols(goto_function.type, partition_iface);

  // Mark accessed global variables as well
  mark_accessed_global_symbols(identifier, partition_iface);
  
  if (goto_function.type.return_type().id() != ID_empty) {
    // Add return value assignment from a temporary variable and
    // store the temporary return value symbol somewhere (so that we can
    // use it later, when processing the deferred function).
    return_assignment_and_mark(goto_function.type, state, nullptr,
            partition_iface, true);
  } else {
    partition_iface.retval_symbol = symbol_exprt();
  }
  // Add also new assignments to all modified global variables
  modified_globals_assignment_and_mark(identifier, state, partition_iface);
}

/*******************************************************************

 Function: symex_assertion_sumt::assign_function_arguments

 Inputs:

 Outputs:

 Purpose: Assigns function arguments to new symbols, also makes
 assignment of the new symbol of return value to the lhs of
 the call site (if any)

\*******************************************************************/
void symex_assertion_sumt::assign_function_arguments(
        statet & state,
        code_function_callt & function_call,
        partition_ifacet & partition_iface)
{
  const irep_idt &identifier=
    to_symbol_expr(function_call.function()).get_identifier();


  // find code in function map
  const goto_functionst::goto_functiont &goto_function = get_function(identifier);

  // Add parameters assignment
  bool old_cp = constant_propagation;
  constant_propagation = false;
  // parameter_assignments is CProver's goto_symex method
  parameter_assignments(identifier, goto_function, state, function_call.arguments());

  // Store the argument renamed symbols somewhere (so that we can use
  // them later, when processing the deferred function).
  mark_argument_symbols(goto_function.type, partition_iface);

  // Mark accessed global variables as well
  mark_accessed_global_symbols(identifier, partition_iface);
  
  if (goto_function.type.return_type().id() != ID_empty) {
    // Needs: DISABLE_OPTIMIZATIONS to work
    //std::cout << "; Before call " << (function_call.lhs().is_nil()) << std::endl;
    //expr_pretty_print(std::cout << "check: ", function_call); std::cout << std::endl;
    //std::cout << (function_call.lhs().get(ID_identifier) == "return'!0") << " and code: " << function_call.pretty() << std::endl;
    // Add return value assignment from a temporary variable and
    // store the temporary return value symbol somewhere (so that we can
    // use it later, when processing the deferred function).
    bool skip_assignment = function_call.lhs().is_nil();
    return_assignment_and_mark(goto_function.type, state, &(function_call.lhs()),
            partition_iface, skip_assignment);
  } else {
    partition_iface.retval_symbol = symbol_exprt();
  }
  // Add also new assignments to all modified global variables
  modified_globals_assignment_and_mark(identifier, state, partition_iface);
  
  constant_propagation = old_cp;
}

/*******************************************************************

 Function: symex_assertion_sumt::mark_argument_symbols

 Purpose: Adds correct (L2) versions of argument symbols to the partition interface

 Assumption: Symbols of the parameters are known to the state and to the namespace
 (They have been used before, e.g. in parameters_assignments, i.e. assigning actual parameters to formal parameters)
\*******************************************************************/
void symex_assertion_sumt::mark_argument_symbols(const code_typet & function_type, partition_ifacet & partition_iface)
{
  for(const auto & parameter : function_type.parameters())
  {
    const auto& identifier = parameter.get_identifier();
    const auto & symbol = get_normal_symbol(identifier);
    auto current_version = get_current_version(symbol);
    partition_iface.argument_symbols.push_back(current_version);

#   if defined(DEBUG_PARTITIONING) && defined(DISABLE_OPTIMIZATIONS)
    expr_pretty_print(std::cout << "Marking argument symbol: ", current_version, "\n");
    std::cout << '\n';
#   endif
    assert(is_L2_SSA_symbol(current_version));
  }
}

/*******************************************************************

 Function: symex_assertion_sumt::mark_accessed_global_symbols

 Purpose: Adds correct (L2) versions of argument symbols to the partition interface

 Assumption: The global symbols are already known to the state and to the namespace

\*******************************************************************/
void symex_assertion_sumt::mark_accessed_global_symbols(const irep_idt & function_id, partition_ifacet & partition_iface)
{
  const auto& globals_accessed = get_accessed_globals(function_id);

  for (auto global_id : globals_accessed) {
    const auto & symbol = get_normal_symbol(global_id);
    // this also stops constant propagation! see method description
    auto current_version = get_current_version(symbol);
    partition_iface.argument_symbols.push_back(current_version);

#   if defined(DEBUG_PARTITIONING) && defined(DISABLE_OPTIMIZATIONS)
    expr_pretty_print(std::cout << "Marking accessed global symbol: ", current_version, "\n");
    std::cout << '\n';
#   endif
    assert(is_L2_SSA_symbol(current_version));
  }
}

/*******************************************************************

 Function: symex_assertion_sumt::modified_globals_assignment_and_mark

 Inputs:

 Outputs:

 Purpose: Assigns values from the modified global variables. Marks the SSA 
 symbol of the global variables for later use when processing the deferred 
 function


\*******************************************************************/
void symex_assertion_sumt::modified_globals_assignment_and_mark(
    const irep_idt &function_id,
    statet &state,
    partition_ifacet &partition_iface)
{
  const auto& globals_modified = get_modified_globals(function_id);

  for (const auto & global_id : globals_modified){
    const auto& symbol = get_normal_symbol(global_id);
    auto ssa_expr = get_next_version(symbol);
    partition_iface.out_arg_symbols.push_back(ssa_expr);

#   if defined(DEBUG_PARTITIONING) && defined(DISABLE_OPTIMIZATIONS)
    expr_pretty_print(std::cout << "Marking modified global symbol: ", ssa_expr);
    std::cout << '\n';
#   endif
    assert(is_L2_SSA_symbol(ssa_expr)); // KE: avoid creating junk
  }
}

/*******************************************************************

 Function: symex_assertion_sumt::return_assignment_and_mark

 Inputs:

 Outputs:

 Purpose: Assigns return value from a new SSA symbols to the lhs at
 call site. Marks the SSA symbol of the return value temporary
 variable for later use when processing the deferred function

\*******************************************************************/
void symex_assertion_sumt::return_assignment_and_mark(
  const code_typet & function_type,
  statet & state,
  const exprt * lhs,
  partition_ifacet & partition_iface,
  bool skip_assignment) {
  assert(function_type.return_type().is_not_nil());

//  const typet & type = function_type.return_type();
  const irep_idt & function_id = partition_iface.function_id;
  const irep_idt retval_symbol_id { as_string(function_id) + "::" + HifrogStringConstants::FUN_RETURN };

  // return_value - create new symbol with versions to support unwinding
  if(!knows_artificial_symbol(retval_symbol_id)){
    create_new_artificial_symbol(retval_symbol_id, function_type.return_type(), true);
  }
  ssa_exprt retval_symbol = get_next_version(retval_symbol_id);

  // Connect the return value to the variable in the calling site
  if (!skip_assignment) {
    code_assignt assignment(*lhs, retval_symbol);
    // Needs DISABLE_OPTIMIZATIONS to work
    //expr_pretty_print(std::cout << "lhs: ", assignment.lhs()); std::cout << std::endl;
    //expr_pretty_print(std::cout << "rhs: ", assignment.rhs()); std::cout << std::endl;

    assert(base_type_eq(assignment.lhs().type(),
                        assignment.rhs().type(), ns));

    bool old_cp = constant_propagation;
    constant_propagation = false;
    symex_assign(state, assignment);
    constant_propagation = old_cp;
  }
# if defined(DEBUG_PARTITIONING) && defined(DISABLE_OPTIMIZATIONS)
  expr_pretty_print(std::cout << "Marking return symbol: ", retval_symbol);
//      expr_pretty_print(std::cout << "Marking return tmp symbol: ", retval_tmp);
  std::cout << '\n';
# endif
  partition_iface.retval_symbol = retval_symbol;
  partition_iface.returns_value = true;
}

/*******************************************************************

 Function: symex_assertion_sumt::store_modified_globals

 Inputs:

 Outputs:

 Purpose: Assigns modified globals to the corresponding temporary SSA 
 symbols.

 FIXME: unify rename/SSA fabrication
\*******************************************************************/
void symex_assertion_sumt::store_modified_globals(
        statet &state,
        const deferred_functiont &deferred_function)
{
  // MB: constant propagation is used only in state.assignment,
  // but we are deliberately working around it, because we already have proper L2 lhs and do not want to modify it
//  bool old_cp = constant_propagation;
//  constant_propagation = false;
  const partition_ifacet &partition_iface = deferred_function.partition_iface;

  for (const auto & out_symbol : partition_iface.out_arg_symbols) {
    // get original symbol expression
    const ssa_exprt & iface_symbol_version = to_ssa_expr(out_symbol);
    const symbol_exprt & rhs  = to_symbol_expr(iface_symbol_version.get_original_expr());
    assert(ns.follow(out_symbol.type()) == ns.follow(rhs.type()));
    // Emit the assignment
    raw_assignment(state, iface_symbol_version, rhs, ns);
  }
//  constant_propagation = old_cp;
}

/*******************************************************************

 Function: symex_assertion_sumt::store_return_value

 Inputs:

 Outputs:

 Purpose: Assigns return value to the corresponding temporary SSA
 symbol

\*******************************************************************/
void symex_assertion_sumt::store_return_value(
        statet &state,
        const deferred_functiont &deferred_function)
{
  const partition_ifacet &partition_iface = deferred_function.partition_iface;
  
  if (!partition_iface.returns_value)
    return;
  
  const ssa_exprt & lhs = to_ssa_expr(partition_iface.retval_symbol);
  const auto& rhs = to_symbol_expr(state.top().return_value);
  
  assert( ns.follow(lhs.type()) == ns.follow(rhs.type()));

  // MB: constant propagation is used only in state.assignment,
  // but we are deliberately working around it, because we already have proper L2 lhs and do not want to modify it
//  bool old_cp = constant_propagation;
//  constant_propagation = false;

  // Emit the assignment
  raw_assignment(state, lhs, rhs, ns);
//  constant_propagation = old_cp;
}
/*******************************************************************

 Function: symex_assertion_sumt::clear_locals_versions

 Inputs:

 Outputs:

 Purpose: Clear local symbols from the l2 cache.

\*******************************************************************/
void symex_assertion_sumt::clear_locals_versions(statet &state)
{
  if (current_call_tree_node->get_function_id() != ID_nil) {
#   ifdef DEBUG_PARTITIONING
    std::cerr << "Level2 size: " << state.level2.current_names.size() << std::endl;
#   endif
    // Clear locals from l2 cache
    for (const auto & local_id : state.top().local_objects) {

#     ifdef DEBUG_PARTITIONING
/*      std::cerr << "Removing local:" << *it << " (" << 
              state.top().level1.get_original_name(local_id) << "): " <<
              (state.level2.current_names.find(local_id) !=
              state.level2.current_names.end()) << std::endl;
*/
#     endif

      statet::level2t::current_namest::const_iterator it2 =
          state.level2.current_names.find(local_id);
      // FIXME: MB: test if this behaviour is correct
      if(it2 != state.level2.current_names.end())
        state.level2.current_names[local_id].first.remove_level_2();
    }
  }
}

/*******************************************************************

 Function: symex_assertion_sumt::handle_function_call

 Inputs:

 Outputs:

 Purpose: Processes a function call based on the corresponding
 summary type

\*******************************************************************/
void symex_assertion_sumt::handle_function_call(
        statet &state,
        code_function_callt &function_call)
{
  // What are we supposed to do with this precise function call? 

  // get call_tree_node corresponding to the called function
  call_tree_nodet &call_tree_node = current_call_tree_node->get_call_sites().find(
      state.source.pc)->second;
  assert(get_current_deferred_function().partition_iface.partition_id != NO_PARTITION_ID);

  // Clean expressions in the arguments, function name, and lhs (if any)
  if (function_call.lhs().is_not_nil()) {
    clean_expr(function_call.lhs(), state, true);
  }

//  MB: I do not think we need to clean expression representing the name of the function
//  clean_expr(function_call.function(), state, false);

  for(auto& expr : function_call.arguments()){
    clean_expr(expr, state, false);
  }

  const irep_idt& function_id = function_call.function().get(ID_identifier);
  const goto_functionst::goto_functiont &goto_function = get_function(function_id);

  // Do we have the body?
  if(!goto_function.body_available())
  {
    no_body(function_id);
   
    if (function_call.lhs().is_not_nil())
    {
      exprt rhs = exprt("nondet_symbol", function_call.lhs().type());
      rhs.set(ID_identifier, "symex::" + std::to_string(nondet_count++));
      
      // KE: I think that's how it is done now - from expr.h
      //rhs.source_location() = function_call.source_location();
      rhs.add_source_location() = function_call.source_location(); 
      
      code_assignt code(function_call.lhs(), rhs);
      symex_assign(state, code);      
    }
    return;
  }

    // created a new deferred_function for this call
    deferred_functiont deferred_function{call_tree_node,
                                         new_partition_iface(call_tree_node,
                                                             get_current_deferred_function().partition_iface.partition_id,
                                                             equation.get_SSA_steps_count())};

  // KE: to support loops, we not only checking the location,
  //     but also if we are in loop. E.g., while(1) { assert(x>5); func2updateX(x); }
  loc = call_tree_node.get_call_location();
  // Assign function parameters and return value
  assign_function_arguments(state, function_call, deferred_function.partition_iface);

  // KE: need it for both cases, when we have the function, and when we don't have it
  bool is_deferred_func = (call_tree_node.get_call_location() < last_assertion_loc) ||
                          ((is_unwind_loop(state) || get_current_deferred_function().call_tree_node.is_in_loop())
                           && (max_unwind != 1));
  if(is_deferred_func){
    switch (call_tree_node.get_precision()){
    case HAVOC:
      havoc_function_call(deferred_function, state, function_id);
      break;
    case SUMMARY:
      if (call_tree_node.is_preserved_node()){
        summarize_function_call(deferred_function, state, function_id);
      } else {
        inline_function_call(deferred_function, state, function_id);
      }
      break;
    case INLINE:
      inline_function_call(deferred_function, state, function_id);
      break;
    default:
      assert(false);
      break;
    }
  }

  //      if(call_tree_node.is_unwind_exceeded())
  //      {
  //        if(options.get_bool_option("unwinding-assertions"))
  //          claim(false_exprt(), "recursion unwinding assertion", state);
  //      }
}

/*******************************************************************

 Function: symex_assertion_sumt::summarize_function_call

 Inputs:

 Outputs:

 Purpose: Summarizes the given function call

\*******************************************************************/
void symex_assertion_sumt::summarize_function_call(
        deferred_functiont& deferred_function,
        statet& state,
        const irep_idt& function_id)
{
  // We should use an already computed summary as an abstraction
  // of the function body
  log.statistics() << "*** SUMMARY abstraction used for function: " << function_id.c_str() << log.eom;
  
  partition_ifacet &partition_iface = deferred_function.partition_iface;

  produce_callsite_symbols(partition_iface, state);
  produce_callend_assumption(partition_iface, state);

  log.statistics() << "Substituting interpolant" << log.eom;

  partition_idt partition_id = equation.reserve_partition(partition_iface);
  assert(summary_store.has_summaries(id2string(function_id)));
    equation.fill_summary_partition(partition_id, summary_store.get_summaries(id2string(function_id)));
}

/*******************************************************************

 Function: symex_assertion_sumt::fill_inverted_summary

 Inputs:

 Outputs:

 Purpose: Prepares a partition with an inverted summary. This is used
 to verify that a function still implies its summary (in upgrade check).

\*******************************************************************/
//void symex_assertion_sumt::fill_inverted_summary(
//        call_tree_nodet& summary_info,
//        statet& state,
//        partition_ifacet& inlined_iface)
//{
//  // We should use an already computed summary as an abstraction
//  // of the function body
//  const irep_idt& function_id = summary_info.get_function_id();
//
//  log.statistics() << "*** INVERTED SUMMARY used for function: " << function_id << log.eom;
//
//  partition_ifacet &partition_iface = new_partition_iface(summary_info, partitiont::NO_PARTITION, 0);
//
//  partition_iface.share_symbols(inlined_iface);
//
//  partition_idt partition_id = equation.reserve_partition(partition_iface);
//
//  log.statistics() << "Substituting interpolant (part:" << partition_id << ")" << log.eom;
//
//  std::string function_name = id2string(function_id);
////# ifdef DEBUG_PARTITIONING
//  log.statistics() << "   summaries available: " << summary_store.get_summaries(function_name).size() << log.eom;
//  log.statistics() << "   summaries used: " << summary_info.get_used_summaries().size() << log.eom;
////# endif
//
//  equation.fill_inverted_summary_partition(partition_id,
//          &summary_store.get_summaries(function_name),
//          summary_info.get_used_summaries());
//}

/*******************************************************************

 Function: symex_assertion_sumt::inline_function_call

 Inputs:

 Outputs:

 Purpose: Inlines the given function call

\*******************************************************************/
void symex_assertion_sumt::inline_function_call(
        deferred_functiont& deferred_function,
        statet& state,
        const irep_idt& function_id)
{
  // We should inline the body --> defer evaluation of the body for later
  log.statistics() << (std::string("*** INLINING function: ") + function_id.c_str()) << log.eom;

  partition_ifacet &partition_iface = deferred_function.partition_iface;

  produce_callsite_symbols(partition_iface, state);
  produce_callend_assumption(partition_iface, state);

  defer_function(deferred_function);
}
/*******************************************************************

 Function: symex_assertion_sumt::havoc_function_call

 Inputs:

 Outputs:

 Purpose: Abstract from the given function call (nondeterministic assignment
 to all the possibly modified variables)

\*******************************************************************/
void symex_assertion_sumt::havoc_function_call(
        deferred_functiont& deferred_function,
        statet& state,
        const irep_idt& function_id)
{
  // We should treat the function as nondeterministic, havocing
  // all data it touches.
  log.statistics() << (std::string("*** NONDET abstraction used for function: ") + function_id.c_str()) << log.eom;

  partition_ifacet &partition_iface = deferred_function.partition_iface;

  produce_callsite_symbols(partition_iface, state);
  produce_callend_assumption(partition_iface, state);

  partition_idt partition_id = equation.reserve_partition(partition_iface);
  equation.fill_stub_partition(partition_id);
}

/*******************************************************************

 Function: symex_assertion_sumt::produce_callsite_symbols

 Inputs:

 Outputs:

 Purpose: Creates new call site (start & end) symbols for the given
 deferred function

\*******************************************************************/
void symex_assertion_sumt::produce_callsite_symbols(
        partition_ifacet& partition_iface,
        statet& state)
{
  irep_idt callstart_id = HifrogStringConstants::CALLSTART_SYMBOL;
  irep_idt callend_id = HifrogStringConstants::CALLEND_SYMBOL;

  // create if not created
  if(!knows_artificial_symbol(callstart_id)){
    create_new_artificial_symbol(callstart_id, typet(ID_bool), true);
  }
  if(!knows_artificial_symbol(callend_id)){
    create_new_artificial_symbol(callend_id, typet(ID_bool), true);
  }

  partition_iface.callstart_symbol = get_next_version(get_artificial_symbol(callstart_id));
  partition_iface.callend_symbol = get_next_version(get_artificial_symbol(callend_id));
  
  if (partition_iface.assertion_in_subtree) {
    irep_idt error_id = HifrogStringConstants::ERROR_SYMBOL;

    if(!knows_artificial_symbol(error_id)){
      create_new_artificial_symbol(error_id, typet(ID_bool), true);
    }
    partition_iface.error_symbol = get_next_version(get_artificial_symbol(error_id));
  }
}

/*******************************************************************

 Function: symex_assertion_sumt::produce_callsite_symbols

 Inputs:

 Outputs:

 Purpose: Inserts assumption that a given call ended (i.e., an assumption of
 the callend symbol)

\*******************************************************************/
void symex_assertion_sumt::produce_callend_assumption(
        const partition_ifacet& partition_iface, statet& state)
{
  exprt tmp(partition_iface.callend_symbol);
  state.guard.guard_expr(tmp);
  target.assumption(state.guard.as_expr(), tmp, state.source);
}

/*******************************************************************

 Function: symex_assertion_sumt::raw_assignment

 Inputs:

 Outputs:

 Purpose: Makes an assignment without increasing the version of the
 lhs symbol (make sure that lhs symbol is not assigned elsewhere)
 
\*******************************************************************/
//void symex_assertion_sumt::raw_assignment(
//        statet &state,
//        exprt &lhs,
//        const exprt &rhs,
//        const namespacet &ns)
//        //bool record_value) = false always!
//{
//  exprt lhs_orig(lhs); // to modify only here
//
//  symbol_exprt rhs_symbol = to_symbol_expr(rhs);
//  rhs_symbol.set(ID_identifier, get_current_l2_name(state, rhs_symbol.get_identifier()));
//
//  assert(lhs_orig.id()==ID_symbol);
//
//  // the type might need renaming
//  ssa_exprt ssa_lhs = ssa_exprt(lhs); // KE: If cause a bug, change lhs_identifier to be without the #1,#2,#3 etc.
//  const irep_idt &lhs_identifier = ssa_lhs.get_identifier();
//
//  state.rename(lhs.type(), lhs_identifier, ns);
//  ssa_lhs.update_type();
//
//  // GF: not sure, just commented this line
//  // KE: it seems that the field of original names isn't in use any more in L2, but is in the state class
//  // const irep_idt &identifier = lhs.get(ID_identifier);
//  // irep_idt l1_identifier=state.level2.get_original_name(identifier);
//  state.get_original_name(lhs_orig);
//  irep_idt l1_identifier = lhs_orig.get(ID_identifier);
//
//  state.propagation.remove(l1_identifier); // pure name
//  // KE: old code, not sure about it!
//
//  // update value sets
//  exprt l1_rhs(rhs_symbol);
//  state.get_l1_name(l1_rhs);
//
//  ssa_exprt l1_lhs(lhs);
//  state.get_l1_name(l1_lhs);
//
//  state.value_set.assign(l1_lhs, l1_rhs, ns, false, false);
//
//  guardt empty_guard;
//  target.assignment(
//    empty_guard.as_expr(),
//    ssa_lhs, //to_symbol_expr(lhs))
//    //to_symbol_expr(ce2),
//    lhs, l1_lhs,
//    rhs_symbol,
//    state.source,
//    symex_targett::assignment_typet::STATE);
//}

void symex_assertion_sumt::raw_assignment(
        statet &state,
        const ssa_exprt &lhs,
        const symbol_exprt &rhs,
        const namespacet &ns)
{

  // inspired by goto_symext::symex_assign_symbol, but we do not want to increment counter on LHS
  // so we do not want the full call to state.assignment
  // also there is no guard here (MB: TODO: what if the function call is in if block?

  // LHS should already be L2 ssa
  assert(!lhs.get_level_2().empty());

  exprt ssa_rhs=rhs;
  state.rename(ssa_rhs, ns);
  do_simplify(ssa_rhs);

  // the following block is what we want from state.assign
  // update value sets
  value_sett::expr_sett rhs_value_set;
  exprt l1_rhs(rhs);
  state.get_l1_name(l1_rhs);

  ssa_exprt l1_lhs(lhs);
  state.get_l1_name(l1_lhs);

  state.value_set.assign(l1_lhs, l1_rhs, ns, false, false);


  // do the assignment

  target.assignment(
    guardt().as_expr(),
    lhs,
    lhs, l1_lhs,
    ssa_rhs,
    state.source,
    symex_targett::assignment_typet::STATE);
}

/*******************************************************************\

Function: symex_assertion_sumt::phi_function

  Inputs:

 Outputs:

 Purpose: Modification of the goto_symext version. In contrast, we
 do not generate Phi functions for dead identifiers.

 Note: to update check goto-symex::phi_function
\*******************************************************************/
void symex_assertion_sumt::phi_function(
  const statet::goto_statet &goto_state,
  statet &dest_state)
{
  // go over all variables to see what changed
  std::unordered_set<ssa_exprt, irep_hash> variables;

  goto_state.level2_get_variables(variables);
  dest_state.level2.get_variables(variables);

  guardt diff_guard;

  if(!variables.empty())
  {
    diff_guard=goto_state.guard;

    // this gets the diff between the guards
    diff_guard-=dest_state.guard;
  }

  for(const auto & variable : variables)
  {
    const irep_idt l1_identifier = variable.get_identifier();
    const irep_idt &obj_identifier = variable.get_object_name();

    if(obj_identifier==guard_identifier)
      continue; // just a guard, don't bother

    if(goto_state.level2_current_count(l1_identifier)==
       dest_state.level2.current_count(l1_identifier))
      continue; // not at all changed

    if (is_dead_identifier(obj_identifier))
      continue;

    // changed!

    // shared variables are renamed on every access anyway, we don't need to
    // merge anything
    const symbolt &symbol=ns.lookup(obj_identifier);

    // shared?
    if(dest_state.atomic_section_id==0 &&
       dest_state.threads.size()>=2 &&
       (symbol.is_shared()))
      continue; // no phi nodes for shared stuff

    // don't merge (thread-)locals across different threads, which
    // may have been introduced by symex_start_thread (and will
    // only later be removed from level2.current_names by pop_frame
    // once the thread is executed)
    if(!variable.get_level_0().empty() &&
       variable.get_level_0()!=std::to_string(dest_state.source.thread_nr))
      continue;

    exprt goto_state_rhs = variable;
    exprt dest_state_rhs = variable;

    {
      auto p_it= goto_state.propagation.values.find(l1_identifier);

      if(p_it!=goto_state.propagation.values.end())
        goto_state_rhs=p_it->second;
      else
        to_ssa_expr(goto_state_rhs).set_level_2(
          goto_state.level2_current_count(l1_identifier));
    }

    {
      goto_symex_statet::propagationt::valuest::const_iterator p_it=
        dest_state.propagation.values.find(l1_identifier);

      if(p_it!=dest_state.propagation.values.end())
        dest_state_rhs=p_it->second;
      else
        to_ssa_expr(dest_state_rhs).set_level_2(
          dest_state.level2.current_count(l1_identifier));
        //dest_state_rhs=symbol_exprt(dest_state.level2.current_name(l1_identifier), type);
    }

    exprt rhs;

    if(dest_state.guard.is_false())
      rhs=goto_state_rhs;
    else if(goto_state.guard.is_false())
      rhs=dest_state_rhs;
    else
    {
      rhs=if_exprt(diff_guard.as_expr(), goto_state_rhs, dest_state_rhs);
      do_simplify(rhs);
    }

    ssa_exprt new_lhs = variable;
    const bool record_events=dest_state.record_events;
    dest_state.record_events=false;
    dest_state.assignment(new_lhs, rhs, ns, true, true); // ++counter l2
    dest_state.record_events=record_events;

    target.assignment(
      true_exprt(),
      new_lhs, new_lhs, new_lhs.get_original_expr(),
      rhs,
      dest_state.source,
      symex_targett::assignment_typet::PHI);
  }
}

/*******************************************************************\

Function: symex_assertion_sumt::claim

  Inputs:

 Outputs:

 Purpose: vcc and claim is the same (one is in the old version
 and one is in the new version)

\*******************************************************************/

void symex_assertion_sumt::vcc(
  const exprt &vcc_expr,
  const std::string &msg,
  statet &state)
{
  total_vccs++;

  exprt expr=vcc_expr;
  
  state.rename(expr, ns);

  if(expr.is_true())
    return;

  state.guard.guard_expr(expr);

  remaining_vccs++;
  target.assertion(state.guard.as_expr(), expr, msg, state.source);
}

/*******************************************************************\

Function: symex_assertion_sumt::end_symex

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
void symex_assertion_sumt::end_symex(statet &state)
{
  store_modified_globals(state, get_current_deferred_function());
  clear_locals_versions(state);
  // Dequeue the current deferred function
  deferred_functions.pop();

  dequeue_deferred_function(state);
}

/*
 Check if in loop or recursion.
 * Fit to the version of Cprover where the unwind counter
 * goes from 0 to (unwind -1). If this changes, then change the
 * method accordingly.
 */
bool symex_assertion_sumt::is_unwind_loop(statet &state)
{
    statet::framet &frame=state.top();

    unsigned int unwind_counter = // KE: for case 3. Not sure, can be the other option
            state.top().loop_iterations[goto_programt::loop_id(*state.source.pc)].count;
    if (frame.loop_iterations[goto_programt::loop_id(*state.source.pc)].count > 0)
    {
        // If we are opening the loop iterations, we are in a loop
        return true;
    } 
    else if (frame.loop_iterations[goto_programt::loop_id(*state.source.pc)].is_recursion)
    {
        // If we are in recursion - we are in a loop, return true
        return true;
    }
    // KE: unwind_counter isn't init, my guess is case 3 described below
    // Either shall be state.top().loop_iterations[goto_programt::loop_id(state.source.pc)].count;
    // OR frame.loop_iterations[goto_programt::loop_id(state.source.pc)].count
    else if (!frame.loop_iterations.empty() && prev_unwind_counter <= unwind_counter)
    {
        // If there are loops in this function, and we are still opening it, we are in a loop
        return true;
    }
    else
    {
        // 1. Not in a loop, 2. Not in recursion, 3. out of loops if unwind 9 --> unwind 0 (e.g.,)
        return false;
    }
}

/*******************************************************************

 Function: symex_assertion_sumt::new_partition_iface

 Inputs:

 Outputs:

 Purpose: Allocate new partition_interface

\*******************************************************************/
partition_ifacet& symex_assertion_sumt::new_partition_iface(call_tree_nodet& call_tree_node,
                                      partition_idt parent_id, unsigned call_loc) {
    auto item = new partition_ifacet(call_tree_node, parent_id, call_loc);
    partition_ifaces.push_back(item);

    auto it = partition_iface_map.find(&call_tree_node);
    if (it == partition_iface_map.end()) {
        it = partition_iface_map.emplace(&call_tree_node, partition_iface_ptrst()).first;
    }
    it->second.push_back(item);
    return *item;
}

/*******************************************************************

 Purpose: Returns the current L2 version of a symbol (can be both artificial or normal (present in the program) symbol)

 Note: Currently, this ensures the constant propagation is turned off for this symbol.
       Otherwise it could return retrieve the constant (current value) instead of current version of the symbol.
       Should be used only in special circumstances, currently when processing interface of functions,
       becuase we do not follow normal data flow there.

\*******************************************************************/
ssa_exprt symex_assertion_sumt::get_current_version(const symbolt & symbol) {
  ssa_exprt ssa = get_l1_ssa(symbol);
  // before renaming to L2, we need to stop constant propagation, otherwise, it could be simplified to a constant,
  // which is not an ssa_exprt anymore
  stop_constant_propagation_for(ssa.get_identifier());
  // get the current L2 version of the L1 symbol
  state.rename(ssa, ns, goto_symex_statet::levelt::L2);
  return ssa;
}

/*******************************************************************

 Purpose: Returns the next L2 version of a symbol (can be both artificial or normal (present in the program) symbol)

 Note: Increases the inner counter keeping track of the current version being used.

\*******************************************************************/
ssa_exprt symex_assertion_sumt::get_next_version(const symbolt & symbol) {
  // get the current L1 version of the symbol
  auto ssa_l1_identifier = get_l1_identifier(symbol);
  assert(state.level2.current_names.find(ssa_l1_identifier) != state.level2.current_names.end());
  state.level2.increase_counter(ssa_l1_identifier);
  // get the correct L2 version after incrementing  the counter
  return get_current_version(symbol);
}

/*******************************************************************

 Purpose: Returns an artificial symbol for tmp_ret_val for the provided partition

 Note: Creates the symbol if it has not been created before

\*******************************************************************/
symbolt symex_assertion_sumt::get_tmp_ret_val_symbol(const partition_ifacet & iface) {
  auto ret_val_id = as_string(iface.function_id) + "::" + HifrogStringConstants::TMP_RETURN;
  // tmp_ret_val is an artificial symbol
  if (!knows_artificial_symbol(ret_val_id)) {
    // we do not treat this as dead, because we need normal behaviour of phi function for tmp_ret_val
    create_new_artificial_symbol(ret_val_id, iface.retval_symbol.type(), false);
  }
  return get_artificial_symbol(ret_val_id);
}

/*******************************************************************

 Purpose: Create new artificial symbol that we want to use but is not present in the code.

 Note: Inserts the new symbol to the symbol_table and prepares the state to know about this new symbol

\*******************************************************************/
void symex_assertion_sumt::create_new_artificial_symbol(const irep_idt & id, const typet & type, bool is_dead) {
  // TODO do we need the location for this symbol? But what location would an artificial symbol had?
  assert(!new_symbol_table.has_symbol(id));
  if(is_dead){
    dead_identifiers.insert(id);
  }
  symbolt symbol;
  symbol.base_name = id;
  symbol.name = id;
  symbol.type = type;
  symbol.is_thread_local = true;

  new_symbol_table.add(symbol);

  // let also state know about the new symbol
  // register the l1 version of the symbol to enable asking for current L2 version
  ssa_exprt l1_ssa = get_l1_ssa(symbol);
  auto l1_id = l1_ssa.get_l1_object_identifier();
  assert(state.level2.current_names.find(l1_id) == state.level2.current_names.end());
  // MB: it seems the CPROVER puts L1 ssa expression as the first of the pair, so we do the same, but I fail to see the reason
  state.level2.current_names[l1_id] = std::make_pair(l1_ssa,0);
}


namespace{

    bool dont_need_globals(const dstringt & fun_name){
        std::string name {fun_name.c_str()};
        return is_cprover_initialize_method(name) || is_main(name);
    }

    struct dstring_lex_ordering
    {
        bool operator()(const dstringt& s1, const dstringt& s2) const
        {
            return s1.compare(s2) < 0;
        }
    };

    using irep_lex_set = std::set<irep_idt, dstring_lex_ordering>;

    void add_to_set_if_global( const namespacet& ns, const exprt& ex,
        irep_lex_set & globals)
    {
        if (ex.id() == ID_symbol) {
            // Directly a symbol - add to set if it is a static variable
            irep_idt id = to_symbol_expr(ex).get_identifier();
            const symbolt& symbol = ns.lookup(id);
            if (symbol.is_static_lifetime && symbol.is_lvalue) {
                globals.insert(id);
            }
        } else if (ex.id() == ID_index) {
            // Indexing scheme
            add_to_set_if_global(ns, to_index_expr(ex).array(), globals);
            add_to_set_if_global(ns, to_index_expr(ex).index(), globals);

        } else if (ex.id() == ID_member) {
            // Structure member scheme
            add_to_set_if_global(ns, to_member_expr(ex).struct_op(), globals);

        } else if (ex.id() == ID_dereference) {
            // Structure member scheme
            add_to_set_if_global(ns, to_dereference_expr(ex).pointer(), globals);

        } else if (ex.id() == ID_typecast || ex.id() == ID_floatbv_typecast) {
            // Typecast
            add_to_set_if_global(ns, to_typecast_expr(ex).op(), globals);

        } else if (ex.id() == ID_constant) {
            // Ignore constants

        } else if (ex.id() == ID_plus) {
            add_to_set_if_global(ns, to_plus_expr(ex).operands()[0], globals);
            add_to_set_if_global(ns, to_plus_expr(ex).operands()[1], globals);

        } else if (ex.id() == ID_minus) {
            add_to_set_if_global(ns, to_minus_expr(ex).operands()[0], globals);
            add_to_set_if_global(ns, to_minus_expr(ex).operands()[1], globals);

        } else if (ex.id() == ID_mod) {
            add_to_set_if_global(ns, to_mod_expr(ex).operands()[0], globals);
            add_to_set_if_global(ns, to_mod_expr(ex).operands()[1], globals);

        } else if (ex.id() == ID_div) {
            add_to_set_if_global(ns, to_div_expr(ex).operands()[0], globals);
            add_to_set_if_global(ns, to_div_expr(ex).operands()[1], globals);

        } else if ((ex.id() == ID_shl) || (ex.id() == ID_ashr) || (ex.id() == ID_lshr)) { // ID_shl, ID_ashr, ID_lshr
            add_to_set_if_global(ns, to_shift_expr(ex).operands()[0], globals);
            add_to_set_if_global(ns, to_shift_expr(ex).operands()[1], globals);

        } else {
            std::cerr << "WARNING: Unsupported operator or index/member scheme - ignoring " << ex.id() << "." << std::endl;
#if defined(DEBUG_GLOBALS) && defined(DISABLE_OPTIMIZATIONS)
            expr_pretty_print(std::cerr << "Expr: ", ex);
    throw "Unsupported indexing scheme.";
#endif
        }
    }
}


void symex_assertion_sumt::add_globals_to_state(statet & state) {
    // get globals
    std::unordered_set<irep_idt, irep_id_hash> globals;
    for (auto & entry : this->accessed_globals) {
        for (auto const & global_id : entry.second) {
            globals.insert(global_id);
        }
    }
    for (auto const & global_id : globals) {
        auto const & symbol = this->ns.lookup(global_id);
        // let's try adding only extern symbols, see if it is enough
        if (symbol.is_extern) {
            // the following is taken from goto_symext::symex_decl
            ssa_exprt ssa(symbol.symbol_expr());
            state.rename(ssa, ns, goto_symex_statet::L1);
            const auto & l1_identifier = ssa.get_identifier();
            state.rename(ssa.type(), l1_identifier, ns);
            ssa.update_type();
            // end of section taken from CPROVER
            assert(state.level2.current_names.find(l1_identifier) == state.level2.current_names.end());
            state.level2.current_names[l1_identifier] = std::make_pair(ssa, 0);
        }
    }
}



void symex_assertion_sumt::analyze_globals() {
    std::unordered_set<irep_idt, irep_id_hash> analyzed_functions;
    analyze_globals_rec(goto_functionst::entry_point(), analyzed_functions);

}

void symex_assertion_sumt::analyze_globals_rec(irep_idt function_to_analyze,
                                               std::unordered_set<irep_idt, irep_id_hash> & analyzed_functions) {
    const auto & body = goto_functions.function_map.at(function_to_analyze).body;
    irep_lex_set globals_read;
    irep_lex_set globals_written;

    // MB: skip body of __CPROVER_initialize and main function, we do not need their globals and they cause some problems
    bool skip = dont_need_globals(function_to_analyze);
    if (!skip) {
        for (const auto & inst : body.instructions) {
            const expr_listt tmp_r = objects_read(inst);
            for (const auto & expr : tmp_r) {
                add_to_set_if_global(ns, expr, globals_read);
            }

            const expr_listt tmp_w = objects_written(inst);
            for (const auto & expr : tmp_w) {
                add_to_set_if_global(ns, expr, globals_read);
                add_to_set_if_global(ns, expr, globals_written);
            }
        }
    }

    analyzed_functions.insert(function_to_analyze);
    for (auto const & inst : body.instructions) {
        if (inst.type != FUNCTION_CALL) {
            continue;
        }

        // NOTE: Expects the function call to be a standard symbol call
        const irep_idt & target_function = to_symbol_expr(
                to_code_function_call(inst.code).function()).get_identifier();

        if (analyzed_functions.find(target_function) == analyzed_functions.end()) {
            analyze_globals_rec(target_function, analyzed_functions);
        }
        if (!skip) {
            const auto & accessed_globals = get_accessed_globals(target_function);
            globals_read.insert(accessed_globals.begin(), accessed_globals.end());
            const auto & modified_globals = get_modified_globals(target_function);
            globals_written.insert(modified_globals.begin(), modified_globals.end());
        }
    }
    auto & accessed = accessed_globals[function_to_analyze];
    assert(accessed.empty());
    std::copy(std::begin(globals_read), std::end(globals_read),
              std::back_inserter(accessed));
    auto & modified = modified_globals[function_to_analyze];
    assert(modified.empty());
    std::copy(std::begin(globals_written), std::end(globals_written),
              std::back_inserter(modified));
}
