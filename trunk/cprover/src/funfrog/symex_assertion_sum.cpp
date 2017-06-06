/*******************************************************************

 Module: Symbolic execution and deciding of a given goto-program
 using and generating function summaries. Based on symex_asserion.cpp

 Author: Ondrej Sery

\*******************************************************************/
    
#include <memory>

#include <time_stopping.h>
#include <expr_util.h>
#include <goto-symex/goto_symex_state.h>
#include <pointer-analysis/add_failed_symbols.h>
#include <util/rename.h> // KE: we should do rename with it, but I didn't find how yet...

#include "partitioning_slice.h"
#include "symex_assertion_sum.h"
#include "expr_pretty_print.h"

/*******************************************************************

 Function: symex_assertion_sumt::~symex_assertion_sumt

 Inputs:

 Outputs:

 Purpose: Delete all allocated partition_ifaces

\*******************************************************************/

symex_assertion_sumt::~symex_assertion_sumt() {
  for (partition_iface_ptrst::iterator it = partition_ifaces.begin();
          it != partition_ifaces.end();
          ++it) {
    delete (*it);
  }
}

/*******************************************************************

 Function: symex_assertion_sumt::loop_free_check

 Inputs:

 Outputs:

 Purpose: Sanity check, we expect loop-free programs only.

\*******************************************************************/

void symex_assertion_sumt::loop_free_check(){
# ifndef NDEBUG
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
    status() << "ASSERTION IS TRUE" << eom;
    return true;
  }

  // Clear the state
  state = goto_symext::statet();

  // Prepare the partitions and deferred functions
  partition_ifacet &partition_iface = new_partition_iface(summary_info, partitiont::NO_PARTITION, 0);
  defer_function(deferred_functiont(summary_info, partition_iface));
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

bool symex_assertion_sumt::prepare_subtree_SSA(const assertion_infot &assertion)
{
  current_assertion = &assertion;

  // Clear the state
  state = goto_symext::statet();

  // Prepare a partition for the ROOT function and defer
  partition_ifacet &partition_iface = new_partition_iface(summary_info, partitiont::NO_PARTITION, 0);
  summary_info.set_inline();
  defer_function(deferred_functiont(summary_info, partition_iface));

  // Make all the interface symbols shared between 
  // the inverted summary and the function.
  prepare_fresh_arg_symbols(state, partition_iface);

  // Prepare a partition for the inverted SUMMARY
  fill_inverted_summary(summary_info, state, partition_iface);

  // Old: ??? state.value_set = value_sets;
  state.source.pc = summarization_context.get_function(
          partition_iface.function_id).body.instructions.begin();
  
  // Plan the function for processing
  dequeue_deferred_function(state);
  
  return process_planned(state, true);
}

/*******************************************************************

 Function: symex_assertion_sumt::refine_SSA

 Inputs:

 Outputs:

 Purpose: Generate SSA statements for the refined program starting from 
 the given set of functions.

\*******************************************************************/

bool symex_assertion_sumt::refine_SSA(const assertion_infot &assertion,
          const std::list<summary_infot*> &refined_functions, bool force_check)
{
  // Defer the functions
  for (std::list<summary_infot*>::const_iterator it = refined_functions.begin();
          it != refined_functions.end();
          ++it) {
    const partition_iface_ptrst* partition_ifaces = get_partition_ifaces(**it);
    assert(!(*it)->is_root());

    if (partition_ifaces) {
      for (partition_iface_ptrst::const_iterator it2 = partition_ifaces->begin();
              it2 != partition_ifaces->end();
              ++it2) {

        partition_ifacet* partition_iface = *it2;

        if (partition_iface->partition_id != partitiont::NO_PARTITION) {
          // assert(equation.get_partitions()[partition_iface->partition_id].summary);
          std::cerr << "Invalidating partition: " << partition_iface->partition_id << std::endl;
          equation.invalidate_partition(partition_iface->partition_id);
        }

        defer_function(deferred_functiont(**it, *partition_iface));
      }
    } else {
      std::cerr << "WARNING: Invalid call to refine_SSA <- " << 
              "refining previously unseen call \"" << 
              (*it)->get_function_id().c_str() << "\" (skipped)" << std::endl;
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
#   if 0
    goto_program.output_instruction(ns, "", std::cout, state.source.pc);
#   endif
    symex_step(summarization_context.get_functions(), state);
  }
  after=current_time();

  status() << "SYMEX TIME: " << (after-before) << eom;

  if(remaining_vccs!=0 || force_check)
  {
    if (use_slicing) {
      before=current_time();
      status() << "All SSA steps: " << equation.SSA_steps.size() << eom;
      partitioning_slice(equation, summarization_context.get_summary_store(), use_smt);
      status() << "Ignored SSA steps after slice: " << equation.count_ignored_SSA_steps() << eom;
      after=current_time();
      status() << "SLICER TIME: " << (after-before) << eom;
    }
  } else {
    status() << "Assertion(s) hold trivially." << eom;
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
 an interpolating solver as separate conjuncts.

\*******************************************************************/

void symex_assertion_sumt::symex_step(
  const goto_functionst &goto_functions,
  statet &state)
{
  assert(!state.threads.empty());
  assert(!state.call_stack().empty());

#ifdef DEBUG_PARTITIONING
  std::cout << "\ninstruction type is " << state.source.pc->type << '\n';
  std::cout << "Location: " << state.source.pc->source_location << '\n';
  std::cout << "Guard: " << from_expr(ns, "", state.guard.as_expr()) << '\n';
  std::cout << "Code: " << from_expr(ns, "", state.source.pc->code) << '\n';
#endif

  const goto_programt::instructiont &instruction=*state.source.pc;
  loc++;
  merge_gotos(state);
  // depth exceeded?
  unsigned max_depth=atoi(options.get_option("depth").c_str());
  if(max_depth!=0 && state.depth>max_depth)
      state.guard.add(false_exprt());
  state.depth++;
   
  // KE: This switch-case is taken from: Function: goto_symext::symex_step
  switch(instruction.type)
  {
  case SKIP:
    if(!state.guard.is_false())
      target.location(state.guard.as_expr(), state.source);
    state.source.pc++;
    break;

  case END_FUNCTION:

    //decrement_unwinding_counter(); 
    store_return_value(state, get_current_deferred_function());
    end_symex(state);
    is_wait_for_end_func = false; // All OK (Return eventually End_Function)
    break;
  
  case LOCATION:
    if(!state.guard.is_false())
      target.location(state.guard.as_expr(), state.source);
    state.source.pc++;
    break;
  
  case GOTO:
    if (do_guard_expl)
    {
        bool store_expln;
        string str;

        store_expln = state.source.pc->guard.has_operands();
        if (store_expln) {
            try { str = from_expr(state.source.pc->guard.op0()); }
            catch (const std::string &s) { str = ""; }
        }
      
        symex_goto(state); // Original code from Cprover follow with break

        if (do_guard_expl &&store_expln && str != "")
        {
            guard_expln[state.guard.as_expr().get("identifier")] = str;
        }
    } else {
        symex_goto(state); // Original code from Cprover follow with break
    }

    break;
    
  case ASSUME:
    if(!state.guard.is_false())
    {
      exprt tmp=instruction.guard;
      clean_expr(tmp, state, false);
      state.rename(tmp, ns);
      symex_assume(state, tmp);
    }

    state.source.pc++;
    break;

  case ASSERT:
    if(!state.guard.is_false())
    {
      if (get_current_deferred_function().summary_info.is_assertion_enabled(state.source.pc)) {
          
        // Skip asserts that are not currently being checked
        if (current_assertion->assertion_matches(state.depth, state.source.pc))
        {
            /* This is the code from ASSERT originally */
            std::string msg=id2string(state.source.pc->source_location.get_comment());
            if(msg=="") 
                msg="assertion";

            exprt tmp(instruction.guard);
            clean_expr(tmp, state, false);
            vcc(tmp, msg, state);
            /* END: This is the code from ASSERT originally */

            /* Optimization to remove code that after the current checked assert + remove any other asserts */
            if ((single_assertion_check  && !get_current_deferred_function().summary_info.is_in_loop()) 
               || (loc >= last_assertion_loc && max_unwind <= 1))
            {
              end_symex(state);
              return;
            }
        }
      }
    }

    state.source.pc++;
    break;
    
  case RETURN:
    if(!state.guard.is_false())
    { 
      return_assignment(state);
      is_wait_for_end_func = true; // Return requires end of func
    }
    
    state.source.pc++;
    break;

  case ASSIGN:      
    if(!state.guard.is_false()) 
      symex_assign_rec(state, to_code_assign(instruction.code));
          
    state.source.pc++;
    break;

  case FUNCTION_CALL:
    assert(!is_wait_for_end_func); // Cannot start a new function if didn't close the old one
    if(!state.guard.is_false())
    {  
      code_function_callt deref_code=
        to_code_function_call(instruction.code);
      // Process the function call according to the call_summary
      handle_function_call(state, deref_code);
    }      
    state.source.pc++;
    break;

  case OTHER:
    if(!state.guard.is_false())
      symex_other(goto_functions, state);

    state.source.pc++;
    break;

  case DECL:
    if(!state.guard.is_false())
      symex_decl(state);

    state.source.pc++;
    break;

  case DEAD:
    // ignore for now
    state.source.pc++;
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
    state.source.pc++;
    break;
  
  case ATOMIC_BEGIN:
  case ATOMIC_END:
    // these don't have path semantics
    state.source.pc++;
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
        const deferred_functiont &deferred_function) 
{
  deferred_functions.push(deferred_function);
  equation.reserve_partition(deferred_function.partition_iface);
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
    current_summary_info = NULL;
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
  current_summary_info = &deferred_function.summary_info;
  const irep_idt& function_id = current_summary_info->get_function_id();
  loc = current_summary_info->get_call_location();

  status () <<  (std::string("Processing a deferred function: ") + function_id.c_str()) << eom;

  // Select symex target equation to produce formulas into the corresponding
  // partition
  equation.select_partition(deferred_function.partition_iface.partition_id);

  // Prepare (and empty) the current state
  state.guard.make_true();

  // Set pc to function entry point
  // NOTE: Here, we expect having the function body available
  const goto_functionst::goto_functiont& function =
    summarization_context.get_function(function_id);
  const goto_programt& body = function.body;
  state.source.pc = body.instructions.begin();
  state.top().end_of_function = --body.instructions.end();
  state.top().goto_state_map.clear();
  state.top().local_objects.clear();

  // Setup temporary store for return value
  if (partition_iface.returns_value) {
    state.top().return_value = partition_iface.retval_tmp;
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

    // Check before getting into symex_assign_symbol that lhs is correct
    assert(lhs.id()==ID_symbol &&
       lhs.get_bool(ID_C_SSA_symbol) &&
       !lhs.has_operands());
      
    guardt guard;
    state.record_events=false;
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
  goto_functionst::function_mapt::const_iterator it =
    summarization_context.get_functions().function_map.find(identifier);

  if(it == summarization_context.get_functions().function_map.end())
    throw "failed to find `"+id2string(identifier)+"' in function_map";

  const goto_functionst::goto_functiont &goto_function=it->second;

  // Callsite symbols
  produce_callsite_symbols(partition_iface, state);

  // Store the argument renamed symbols somewhere (so that we can use
  // them later, when processing the deferred function).
  mark_argument_symbols(goto_function.type, state, partition_iface);

  // Mark accessed global variables as well
  mark_accessed_global_symbols(identifier, state, partition_iface, false);
  
  // FIXME: We need to store the SSA_steps.size() here, so that 
  // SSA_exec_order is correctly ordered.
  // NOTE: The exec_order is not used now.
  
  if (goto_function.type.return_type().id() != ID_empty) {
    // Add return value assignment from a temporary variable and
    // store the temporary return value symbol somewhere (so that we can
    // use it later, when processing the deferred function).
    return_assignment_and_mark(goto_function.type, state, NULL,
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
        statet &state,
        code_function_callt &function_call,
        deferred_functiont &deferred_function)
{
  const irep_idt &identifier=
    to_symbol_expr(function_call.function()).get_identifier();
  partition_ifacet &partition_iface = deferred_function.partition_iface;

  // find code in function map
  goto_functionst::function_mapt::const_iterator it =
    summarization_context.get_functions().function_map.find(identifier);

  if(it == summarization_context.get_functions().function_map.end())
    throw "failed to find `"+id2string(identifier)+"' in function_map";

  const goto_functionst::goto_functiont &goto_function=it->second;

  // Add parameters assignment
  bool old_cp = constant_propagation;
  constant_propagation = false;
  parameter_assignments(identifier, goto_function, state, function_call.arguments());

  // Store the argument renamed symbols somewhere (so that we can use
  // them later, when processing the deferred function).
  mark_argument_symbols(goto_function.type, state, partition_iface);

  // Mark accessed global variables as well
  bool is_init_stage = (id2string(identifier).find("__CPROVER_initialize") != std::string::npos);
  mark_accessed_global_symbols(identifier, state, partition_iface, is_init_stage);
  
  // FIXME: We need to store the SSA_steps.size() here, so that 
  // SSA_exec_order is correctly ordered.
  // NOTE: The exec_order is not used now.
  
  if (goto_function.type.return_type().id() != ID_empty) {
    //std::cout << "; Before call " << (function_call.lhs().is_nil()) << std::endl;
    //expr_pretty_print(std::cout << "check: ", function_call); std::cout << std::endl;
    //std::cout << (function_call.lhs().get(ID_identifier) == "return'!0") << " and code: " << function_call.pretty() << std::endl;
    // Add return value assignment from a temporary variable and
    // store the temporary return value symbol somewhere (so that we can
    // use it later, when processing the deferred function).
    // KE: the nil (function_call.lhs().is_nil()), changed into |return'!0|
    // Fix the flag according to the string return'!0 or is_nil
    // TODO: find what is the right symbol
    bool is_nil_or_ret = ((function_call.lhs().get(ID_identifier) == "return'!0") 
                          || 
                          (function_call.lhs().is_nil()));
    return_assignment_and_mark(goto_function.type, state, &(function_call.lhs()),
            partition_iface, is_nil_or_ret);
  } else {
    partition_iface.retval_symbol = symbol_exprt();
  }
  // Add also new assignments to all modified global variables
  modified_globals_assignment_and_mark(identifier, state, partition_iface);
  
  constant_propagation = old_cp;
}

/*******************************************************************

 Function: symex_assertion_sumt::mark_argument_symbols

 Inputs:

 Outputs:

 Purpose: Marks the SSA symbols of function arguments

\*******************************************************************/
void symex_assertion_sumt::mark_argument_symbols(
        const code_typet &function_type,
        statet &state,
        partition_ifacet &partition_iface)
{
  const code_typet::parameterst &parameter_types=function_type.parameters();
 
  for(code_typet::parameterst::const_iterator
      it=parameter_types.begin();
      it!=parameter_types.end();
      it++)
  {
    const code_typet::parametert &parameter=*it;
    const irep_idt &identifier = parameter.get_identifier();

    const symbolt &symbol = ns.lookup(identifier);
    symbol_exprt lhs = symbol.symbol_expr();
    state.rename(lhs, ns, goto_symex_statet::L1);

    const irep_idt l0_name = lhs.get_identifier();
    statet::level2t::current_namest::const_iterator it2 =
        state.level2.current_names.find(l0_name);
    if(it2==state.level2.current_names.end()) assert (0);

    // rename L2: update the level counters
    ssa_exprt ssa_expr_lhs = to_ssa_expr(lhs);
    state.level0(ssa_expr_lhs, ns, state.source.thread_nr);
    state.level1(ssa_expr_lhs);
    ssa_expr_lhs.set_level_2(state.level2.current_count(ssa_expr_lhs.get_identifier()));

    to_ssa_expr(lhs).set_level_2(it2->second.second);
    partition_iface.argument_symbols.push_back(lhs);

#   ifdef DEBUG_PARTITIONING
    std::cout << "Marking argument symbol: " << symbol << "\n";
#   endif
  }
}


/*******************************************************************

 Function: symex_assertion_sumt::mark_accessed_global_symbols

 Inputs:

 Outputs:

 Purpose: Marks the SSA symbols of accessed globals

\*******************************************************************/
void symex_assertion_sumt::mark_accessed_global_symbols(
    const irep_idt &function_id,
    statet &state,
    partition_ifacet &partition_iface,
    bool is_init_stage) 
{
  const function_infot::lex_sorted_idst& globals_accessed = 
    summarization_context.get_function_info(function_id).get_accessed_globals();
  
  if (globals_accessed.empty())
    return;

  for (function_infot::lex_sorted_idst::const_iterator it =
          globals_accessed.begin();
          it != globals_accessed.end();
          ++it) 
  {
    // The symbol is not yet in l2 renaming - Add it during init stage only
    if (is_init_stage) { // first init, which makes sense to force to 0
        assert (state.level2.current_names.find(*it) == state.level2.current_names.end());
        // Original code: state.level2.rename(*it, 0);
        level2_rename_init(state, (ns.lookup(*it)).symbol_expr());
    } else if (state.level2.current_names.count(*it) == 0) { // after init stage - forcing 0
        level2_rename_init(state, (ns.lookup(*it)).symbol_expr());
        // GF: should there be assert(0) ? 
        // KE: only if the init stage can init - else will assert after this if
#       ifdef DEBUG_PARTITIONING
            std::cerr << "\n * WARNING: Forcing '" << *it << 
              "' into l2 renaming. " << std::endl;
#       endif    
    }

    // Check we have items in *it location
    assert(state.level2.current_names.count(*it) > 0);
    
    // rename: update the level counters: varname!L0
    ssa_exprt ssa_expr = state.level2.current_names[*it].first;
    state.level0(ssa_expr, ns, state.source.thread_nr);
    state.level1(ssa_expr);
    ssa_expr.set_level_2(state.level2.current_count(ssa_expr.get_identifier()));
    
    // Push the new renamed to the partition
    symbol_exprt symb_ex(ssa_expr);
    to_ssa_expr(symb_ex).set_level_2(state.level2.current_count(*it));
    //KE: else some of the global ones are not ssa (but just symbol)
    
    partition_iface.argument_symbols.push_back(symb_ex);
#   ifdef DEBUG_PARTITIONING
    expr_pretty_print(std::cout << "Marking accessed global symbol: ", symb_ex, " ");
#   endif
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
  const function_infot::lex_sorted_idst& globals_modified = 
    summarization_context.get_function_info(function_id).get_modified_globals();
  
  if (globals_modified.empty())
    return;
  
  for (function_infot::lex_sorted_idst::const_iterator it =
          globals_modified.begin();
          it != globals_modified.end();
          ++it) 
  {
    // Creates a var name: varname!L0#L2 - instance and thread  
    const symbolt& symbol = ns.lookup(*it);
    get_new_symbol_version(*it, state, symbol.type);    
    ssa_exprt ssa_expr = state.level2.current_names[*it].first;
    state.level0(ssa_expr, ns, state.source.thread_nr);
    state.level1(ssa_expr);
    ssa_expr.set_level_2(state.level2.current_count(ssa_expr.get_identifier()));
    
    symbol_exprt symb_ex(ssa_expr);
    partition_iface.out_arg_symbols.push_back(symb_ex);

#   ifdef DEBUG_PARTITIONING
    expr_pretty_print(std::cout << "Marking modified global symbol: ", symb_ex);
#   endif
  }
}

/*******************************************************************

 Function: symex_assertion_sumt::level2_rename_and_2ssa

 Inputs:

 Outputs:

 Purpose: Replace the old functionality of rename + new SSA in old
 	  Also adds L2 counter to the symbol and increase L2 counter
 * CProver framework

\*******************************************************************/
void symex_assertion_sumt::level2_rename_and_2ssa(
    statet &state, 
    const irep_idt identifier, 
    const typet& type,
    symbol_exprt& ret_symbol)
{
    // Create a general var: identifier: funfrog::netpoll_trap::\return_value
    ssa_exprt code_var(symbol_exprt(identifier, type));
    
    // Change to SSA format: identifier: funfrog::netpoll_trap::\return_value#2
    code_var.set_identifier(get_new_symbol_version(identifier, state, type)); 
    
    // Adds L2 counter to the symbol (L2: 1 adds to the expression) 
    state.level0(code_var, ns, state.source.thread_nr);
    state.level1(code_var);
    code_var.set_level_2(state.level2.current_count(code_var.get_identifier())); 
    
    // Return a symbol of ssa val with expression of original var
    ret_symbol = to_symbol_expr(code_var);
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
        const code_typet &function_type,
        statet &state,
        const exprt *lhs,
        partition_ifacet &partition_iface,
        bool skip_assignment)
{
    assert(function_type.return_type().is_not_nil());

    const typet& type = function_type.return_type();
    const irep_idt &function_id = partition_iface.function_id;
    irep_idt retval_symbol_id(
            as_string(function_id) + "::#return_value!"); // For goto_symext::symex_assign
    irep_idt retval_tmp_id(
            as_string(function_id) + "::?return_value!::$tmp::"); // tmp in cprover is a token
    
    // Gets a new symbol per function call:
    get_new_name(retval_symbol_id,ns);
    get_new_name(retval_tmp_id,ns);

// Check the symbol was created correctly    
#ifdef DEBUG_PARTITIONING
    if (!_return_vals.empty())
    {
        assert("Return value symbol is in use for another call of this function" 
                && (_return_vals.count(as_string(retval_symbol_id)) == 0));
        assert("Temp return value symbols are in use for another call of this function" 
                && (_return_vals.count(as_string(retval_tmp_id)) == 0));
    }
    _return_vals.insert(as_string(retval_symbol_id));
    _return_vals.insert(as_string(retval_tmp_id));
#endif
    
    // return_value_tmp - create new symbol with versions to support unwinding
    add_symbol(retval_tmp_id, type, false, function_type.source_location());
    symbol_exprt retval_tmp(retval_tmp_id, type);

    // return_value - create new symbol with versions to support unwinding
    add_symbol(retval_symbol_id, type, false, function_type.source_location()); // Need to be in the table since rename l0 needs it
    symbol_exprt retval_symbol;	
    level2_rename_and_2ssa(state, retval_symbol_id, type, retval_symbol); // We do rename alone...
    
    // Connect the return value to the variable in the calling site 
    if (!skip_assignment) {
        code_assignt assignment(*lhs, retval_symbol);
        //expr_pretty_print(std::cout << "lhs: ", assignment.lhs()); std::cout << std::endl;
        //expr_pretty_print(std::cout << "rhs: ", assignment.rhs()); std::cout << std::endl;

        assert(base_type_eq(assignment.lhs().type(),
                assignment.rhs().type(), ns));

        bool old_cp = constant_propagation;
        constant_propagation = false;
        symex_assign(state, assignment);
        constant_propagation = old_cp;
    } 
    # ifdef DEBUG_PARTITIONING
      expr_pretty_print(std::cout << "Marking return symbol: ", retval_symbol);
      expr_pretty_print(std::cout << "Marking return tmp symbol: ", retval_tmp);
    # endif

    partition_iface.retval_symbol = retval_symbol;
    partition_iface.retval_tmp = retval_tmp;
    partition_iface.returns_value = true;
}

/*******************************************************************

 Function: symex_assertion_sumt::store_modified_globals

 Inputs:

 Outputs:

 Purpose: Assigns modified globals to the corresponding temporary SSA 
 symbols.

\*******************************************************************/
void symex_assertion_sumt::store_modified_globals(
        statet &state,
        const deferred_functiont &deferred_function)
{
  // Emit the assignment
  bool old_cp = constant_propagation;
  constant_propagation = false;
  partition_ifacet &partition_iface = deferred_function.partition_iface;
  
  state.record_events=false; // expr-s are build ins 
  // therefore we don't want to use parallel built-ins
  for (std::vector<symbol_exprt>::const_iterator it = 
          partition_iface.out_arg_symbols.begin();
          it != partition_iface.out_arg_symbols.end();
          ++it) {
 
    //symbol_exprt rhs(state.get_original_name(it->get_identifier()), 
    //        ns.follow(it->type())); 
        
    // SSA Symbol - copy so (*it) is the same after this code!
    symbol_exprt lhs_ssa_symbol(*it);  
      
    // Pure Symbol
    symbol_exprt rhs_ssa_symbol(*it);  
    state.get_original_name(rhs_ssa_symbol); // KE: Don't like this solution, but that's the only way it works        
    symbol_exprt rhs_symbol(ssa_exprt(rhs_ssa_symbol).get(ID_identifier), ns.follow(rhs_ssa_symbol.type()));   
      
    code_assignt assignment(
            lhs_ssa_symbol,
            rhs_symbol);

    assert( ns.follow(assignment.lhs().type()) ==
            ns.follow(assignment.rhs().type()));

    raw_assignment(state, assignment.lhs(), assignment.rhs(), ns);    
  }
  constant_propagation = old_cp;
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
  partition_ifacet &partition_iface = deferred_function.partition_iface;
  
  if (!partition_iface.returns_value)
    return;
  
  code_assignt assignment(
          partition_iface.retval_symbol,
          partition_iface.retval_tmp);
  
  assert( ns.follow(assignment.lhs().type()) ==
          ns.follow(assignment.rhs().type()));
  
  // Emit the assignment
  bool old_cp = constant_propagation;
  constant_propagation = false;
  raw_assignment(state, assignment.lhs(), assignment.rhs(), ns);
  constant_propagation = old_cp;
}
/*******************************************************************

 Function: symex_assertion_sumt::clear_locals_versions

 Inputs:

 Outputs:

 Purpose: Clear local symbols from the l2 cache.

\*******************************************************************/
void symex_assertion_sumt::clear_locals_versions(statet &state)
{
  if (current_summary_info->get_function_id() != ID_nil) {
    // Clear locals from l2 cache
    const std::set<irep_idt>& local_identifiers = state.top().local_objects;

#   ifdef DEBUG_PARTITIONING
    std::cerr << "Level2 size: " << state.level2.current_names.size() << std::endl;
#   endif
    for (std::set<irep_idt>::const_iterator
      it = local_identifiers.begin();
            it != local_identifiers.end();
            ++it) {

#     ifdef DEBUG_PARTITIONING
/*      std::cerr << "Removing local:" << *it << " (" << 
              state.top().level1.get_original_name(*it) << "): " <<
              (state.level2.current_names.find(*it) !=
              state.level2.current_names.end()) << std::endl;
*/
#     endif

      statet::level2t::current_namest::const_iterator it2 =
          state.level2.current_names.find(*it);
      if(it2 != state.level2.current_names.end())
        state.level2.current_names[*it].first.remove_level_2();
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

  summary_infot &summary_info = current_summary_info->get_call_sites().find(
      state.source.pc)->second;
  assert(get_current_deferred_function().partition_iface.partition_id != partitiont::NO_PARTITION);
  deferred_functiont deferred_function(summary_info, 
          new_partition_iface(summary_info, 
          get_current_deferred_function().partition_iface.partition_id, 
          equation.get_SSA_steps_count()));
  const irep_idt& function_id = function_call.function().get(ID_identifier);
  const goto_functionst::goto_functiont &goto_function =
    summarization_context.get_function(function_id);
  
  // Clean expressions in the arguments, function name, and lhs (if any)
  if (function_call.lhs().is_not_nil())
    clean_expr(function_call.lhs(), state, true);

  clean_expr(function_call.function(), state, false);

  Forall_expr(it, function_call.arguments())
  clean_expr(*it, state, false);

  // Do we have the body?
  if(!goto_function.body_available())
  {
    no_body(function_id);

    if(function_call.lhs().is_not_nil())
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

  loc = summary_info.get_call_location();
  // Assign function parameters and return value
  assign_function_arguments(state, function_call, deferred_function);
  if(summary_info.get_call_location() < last_assertion_loc){
    switch (summary_info.get_precision()){
    case HAVOC:
      havoc_function_call(deferred_function, state, function_id);
      break;
    case SUMMARY:
      if (summary_info.is_preserved_node()){
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

  //      if(summary_info.is_unwind_exceeded())
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
  status() << "*** SUMMARY abstraction used for function: " << function_id.c_str() << eom;
  
  partition_ifacet &partition_iface = deferred_function.partition_iface;

  produce_callsite_symbols(partition_iface, state);
  produce_callend_assumption(partition_iface, state);

  status() << "Substituting interpolant" << eom;

  partition_idt partition_id = equation.reserve_partition(partition_iface);
  equation.fill_summary_partition(partition_id,
          &summarization_context.get_summaries(function_id));
}

/*******************************************************************

 Function: symex_assertion_sumt::fill_inverted_summary

 Inputs:

 Outputs:

 Purpose: Prepares a partition with an inverted summary. This is used
 to verify that a function still implies its summary (in upgrade check).

\*******************************************************************/
void symex_assertion_sumt::fill_inverted_summary(
        summary_infot& summary_info,
        statet& state,
        partition_ifacet& inlined_iface)
{
  // We should use an already computed summary as an abstraction
  // of the function body
  const irep_idt& function_id = summary_info.get_function_id();

  status() << "*** INVERTED SUMMARY used for function: " << function_id << eom;
  
  partition_ifacet &partition_iface = new_partition_iface(summary_info, partitiont::NO_PARTITION, 0);
  
  std::cout << ";; Call test 123 " << std::endl;
  partition_iface.share_symbols(inlined_iface);

  partition_idt partition_id = equation.reserve_partition(partition_iface);

  status() << "Substituting interpolant (part:" << partition_id << ")" << eom;

//# ifdef DEBUG_PARTITIONING
  status() << "   summaries available: " << summarization_context.get_summaries(function_id).size() << eom;
  status() << "   summaries used: " << summary_info.get_used_summaries().size() << eom;
//# endif

  equation.fill_inverted_summary_partition(partition_id,
          &summarization_context.get_summaries(function_id),
          summary_info.get_used_summaries());
}

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
  status() << (std::string("*** INLINING function: ") + function_id.c_str()) << eom;

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
  status() << (std::string("*** NONDET abstraction used for function: ") + function_id.c_str()) << eom;

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
# ifdef DEBUG_PARTITIONING
  irep_idt callstart_id = "hifrog::" + as_string(partition_iface.function_id) +
          "::?callstart_symbol";
  irep_idt callend_id = "hifrog::" + as_string(partition_iface.function_id) +
          "::?callend_symbol";
  irep_idt error_id = "hifrog::" + as_string(partition_iface.function_id) +
          "::?error_symbol";
# else
  irep_idt callstart_id = "hifrog::?fun_start";
  irep_idt callend_id = "hifrog::?fun_end";
  irep_idt error_id = "hifrog::?err";
# endif

  partition_iface.callstart_symbol.set_identifier(
          get_new_symbol_version(callstart_id, state,typet(ID_bool)));
  partition_iface.callend_symbol.set_identifier(
          get_new_symbol_version(callend_id, state,typet(ID_bool)));

  add_symbol(callstart_id, typet(ID_bool), true, partition_iface.callstart_symbol.source_location());
  add_symbol(callend_id, typet(ID_bool), true, partition_iface.callend_symbol.source_location());
  
  if (partition_iface.assertion_in_subtree) {
    partition_iface.error_symbol.set_identifier(
          get_new_symbol_version(error_id, state,typet(ID_bool)));
    add_symbol(error_id, typet(ID_bool), true, partition_iface.error_symbol.source_location());
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

 Function: symex_assertion_sumt::level2_rename

 Inputs: State and a symbol in use for the first time

 Outputs: --

 Purpose: to do this Original code: state.level2.rename(*it, 0);
          in cprover 5.5 version
  
 Taken from goto_symext::symex_decl

\*******************************************************************/
void symex_assertion_sumt::level2_rename_init(statet &state, const symbol_exprt &expr) 
{        
    ssa_exprt ssa(expr);
    const irep_idt &l1_identifier=ssa.get_identifier();

    // Must be the first time the var is in use
    assert (state.level2.current_names.find(l1_identifier)== 
                state.level2.current_names.end());
    
    // Set the counter to be 0 (val_name#0)
    state.level2.current_names[l1_identifier]=std::make_pair(ssa, 0);

    state.rename(ssa.type(), l1_identifier, ns);
    ssa.update_type();
    
    // Adds L2 counter to the SSA expression (L2: 0)
    ssa.set_level_2(state.level2.current_count(l1_identifier)); // Adds L2 counter to the symbol
    
    // in case of pointers, put something into the value set - else got "symbol" as name?!
    if(ns.follow(expr.type()).id()==ID_pointer)
    {
      exprt failed=
        get_failed_symbol(expr, ns);

      exprt rhs;

      if(failed.is_not_nil())
      {
        address_of_exprt address_of_expr;
        address_of_expr.object()=failed;
        address_of_expr.type()=expr.type();
        rhs=address_of_expr;
      }
      else
        rhs=exprt(ID_invalid);

      state.rename(rhs, ns, goto_symex_statet::L1);
      state.value_set.assign(ssa, rhs, ns, true, false);
    }
}
/*******************************************************************

 Function: symex_assertion_sumt::get_new_symbol_version

 Inputs:

 Outputs:

 Purpose: Helper function for renaming of an identifier without
 assigning to it. Constant propagation is stopped for the given symbol.

\*******************************************************************/
irep_idt symex_assertion_sumt::get_new_symbol_version(
        const irep_idt& identifier,
        statet &state,
        typet type)
{
    //--8<--- Taken from goto_symex_statet::assignment()

    // Force Rename
    if(state.level2.current_names.find(identifier)==state.level2.current_names.end())
        level2_rename_init(state, symbol_exprt(identifier, type));
    
    // rename
    state.level2.increase_counter(identifier);
    
    // Break constant propagation for this new symbol
    state.propagation.remove(identifier);

    // Return Value, or any other SSA symbol. From version 5.6 of cbmc an index always starts in 0
    irep_idt new_l2_name = id2string(identifier) + "#" + std::to_string(state.level2.current_count(identifier));
  
    return new_l2_name;
}

// Simplify what the old code of state L2 current_name does - it is only a stupid test that
// We always with a counter!
irep_idt symex_assertion_sumt::get_current_l2_name(statet &state, const irep_idt &identifier) const 
{
    if (id2string(identifier).find("#") != std::string::npos)
        return identifier;
    
    return id2string(identifier)+"#"+std::to_string(state.level2.current_count(identifier));
}

/*******************************************************************

 Function: symex_assertion_sumt::raw_assignment

 Inputs:

 Outputs:

 Purpose: Makes an assignment without increasing the version of the
 lhs symbol (make sure that lhs symbol is not assigned elsewhere)
 
\*******************************************************************/
void symex_assertion_sumt::raw_assignment(
        statet &state,
        exprt &lhs,
        const exprt &rhs,
        const namespacet &ns)
        //bool record_value) = false always!
{
  exprt lhs_orig(lhs); // to modify only here
  
  symbol_exprt rhs_symbol = to_symbol_expr(rhs);
  rhs_symbol.set(ID_identifier, get_current_l2_name(state, rhs_symbol.get_identifier()));

  assert(lhs_orig.id()==ID_symbol);

  // the type might need renaming
  ssa_exprt ssa_lhs = ssa_exprt(lhs); // KE: If cause a bug, change lhs_identifier to be without the #1,#2,#3 etc.
  const irep_idt &lhs_identifier = ssa_lhs.get_identifier();

  state.rename(lhs.type(), lhs_identifier, ns);
  ssa_lhs.update_type();

  // GF: not sure, just commented this line
  // KE: it seems that the field of original names isn't in use any more in L2, but is in the state class
  // const irep_idt &identifier = lhs.get(ID_identifier);
  // irep_idt l1_identifier=state.level2.get_original_name(identifier);
  state.get_original_name(lhs_orig);
  irep_idt l1_identifier = lhs_orig.get(ID_identifier);

  state.propagation.remove(l1_identifier); // pure name
  // KE: old code, not sure about it!
  
  // update value sets
  exprt l1_rhs(rhs_symbol);
  state.get_l1_name(l1_rhs);

  ssa_exprt l1_lhs(lhs);
  state.get_l1_name(l1_lhs);

  state.value_set.assign(l1_lhs, l1_rhs, ns, false, false);

  guardt empty_guard;
  target.assignment(
    empty_guard.as_expr(),
    ssa_lhs, //to_symbol_expr(lhs))
    //to_symbol_expr(ce2),
    lhs, l1_lhs,
    rhs_symbol,
    state.source,
    symex_targett::assignment_typet::STATE);
}

/*******************************************************************\

Function: symex_assertion_sumt::phi_function

  Inputs:

 Outputs:

 Purpose: Modification of the goto_symext version. In contrast, we
 do not generate Phi functions for dead identifiers.

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

  for(std::unordered_set<ssa_exprt, irep_hash>::const_iterator
      it=variables.begin();
      it!=variables.end();
      it++)
  {
    const irep_idt l1_identifier=it->get_identifier();
    const irep_idt &obj_identifier=it->get_object_name();

    if(obj_identifier==guard_identifier)
      continue; // just a guard, don't bother

    if(goto_state.level2_current_count(l1_identifier)==
       dest_state.level2.current_count(l1_identifier))
      continue; // not at all changed

    if (is_dead_identifier(l1_identifier))
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
    if(!it->get_level_0().empty() &&
       it->get_level_0()!=std::to_string(dest_state.source.thread_nr))
      continue;

    exprt goto_state_rhs=*it, dest_state_rhs=*it;

    {
      goto_symex_statet::propagationt::valuest::const_iterator p_it=
        goto_state.propagation.values.find(l1_identifier);

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

    ssa_exprt new_lhs=*it;
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

 Purpose:

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

void symex_assertion_sumt::end_symex(statet &state)
{
  store_modified_globals(state, get_current_deferred_function());
  clear_locals_versions(state);
  // Dequeue the current deferred function
  deferred_functions.pop();

  dequeue_deferred_function(state);
}
