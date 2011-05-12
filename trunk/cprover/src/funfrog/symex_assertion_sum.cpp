/*******************************************************************

 Module: Symbolic execution and deciding of a given goto-program
 using and generating function summaries. Based on symex_asserion.cpp

 Author: Ondrej Sery

\*******************************************************************/
    
#include <memory>

#include <goto-symex/build_goto_trace.h>
#include <find_symbols.h>
#include <ansi-c/expr2c.h>
#include <time_stopping.h>
#include <solvers/sat/satcheck.h>
#include <solvers/smt1/smt1_dec.h>
#include <loopfrog/memstat.h>
#include <expr_util.h>
#include <i2string.h>

#include "partitioning_slice.h"
#include "symex_assertion_sum.h"
#include "expr_pretty_print.h"

fine_timet global_satsolver_time;
fine_timet global_sat_conversion_time;

//#define DEBUG_PARTITIONING

/*******************************************************************

 Function: symex_assertion_sumt::assertion_holds

 Inputs:

 Outputs:

 Purpose: Checks if the given assertion of the GP holds

\*******************************************************************/

bool symex_assertion_sumt::assertion_holds(
  const goto_programt &goto_program,
  const assertion_infot &assertion,
  std::ostream &out,
  unsigned long &max_memory_used,
  bool use_smt,
  bool use_slicing)
{
  stream_message_handlert message_handler(out);
  current_assertion = &assertion;

  // these are quick...
  if(assertion.get_location()->guard.is_true())
  {
    out << std::endl << "ASSERTION IS TRUE" << std::endl;
    return true;
  }

  goto_programt::const_targett last = assertion.get_location(); last++;

# ifndef NDEBUG
  // sanity check, we expect loop-free programs only.
  forall_goto_program_instructions(it, goto_program)
    assert(!it->is_backwards_goto());
  forall_goto_functions(it, summarization_context.get_functions()) {
    forall_goto_program_instructions(it2, it->second.body) {
      if (it2->is_backwards_goto()) {
        std::cerr << "ERROR: Backward goto (i.e., a loop) in function: " << it->first << std::endl;
        goto_program.output_instruction(ns, "", out, it2);
        // assert(!it2->is_backwards_goto());
      }
    }
  }
# endif

  // Proceed with symbolic execution
  fine_timet before, after;
  before=current_time();

  goto_symext::statet state;
  // Prepare for the pc++ after returning from the last END_FUNCTION
  state.top().calling_location = --goto_program.instructions.end();

  // Prepare the partitions and deferred functions
  defer_function(deferred_functiont(summary_info), ID_nil);
  equation.select_partition(deferred_functions.front().partition_id);

  // Old: ??? state.value_set = value_sets;

  // FIXME: If we care only about a single assertion, we should stop 
  // as soon as it is reached.
  for(state.source.pc = goto_program.instructions.begin();
      has_more_steps(state);
      )
  {
#   if 0
    goto_program.output_instruction(ns, "", std::cout, state.source.pc);
#   endif
    symex_step(summarization_context.get_functions(), state);
    // state.value_set.output(ns, std::cout);
  }
  after=current_time();

  if(out.good())
    out << "SYMEX TIME: "<< time2string(after-before) << std::endl;

  bool sat=false;

  decider.set_message_handler(message_handler);
  decider.set_verbosity(10);

  if(remaining_claims!=0)
  {
    if (use_slicing) {
      before=current_time();
      out << "All SSA steps: " << equation.SSA_steps.size() << std::endl;
      partitioning_slice(equation);
      out << "Ignored SSA steps after slice: " << equation.count_ignored_SSA_steps() << std::endl;
      after=current_time();
      if (out.good())
        out << "SLICER TIME: "<< time2string(after-before) << std::endl;
    }


    fine_timet before,after;
    before=current_time();
    equation.convert(decider, interpolator);
    after=current_time();
    global_sat_conversion_time += (after-before);

    if (out.good())
      out << "CONVERSION TIME: "<< time2string(after-before) << std::endl;

    // Decides the equation
    sat = is_satisfiable(decider, out);
  } else {
      out << "Assertion(s) are trivially unreachable." << std::endl;
  }

  unsigned long this_mem = current_memory();
  if (this_mem > max_memory_used)
    max_memory_used = this_mem;

  if (!sat)
  {
    if (out.good())
      out << std::endl << "ASSERTION IS TRUE" << std::endl;
    return true;
  }
  else
  {
    // Builds the trace if it is SAT
    goto_tracet trace;
    build_goto_trace(equation, decider, trace);
    if (out.good())
      show_goto_trace(out, ns, trace);

    if (out.good())
      out << std::endl << "NONDET assigns:" << std::endl;

    unsigned int nondet_counter=0;
    std::set<exprt> lhs_symbols;
    find_symbols(assertion.get_location()->guard, lhs_symbols);

    if (lhs_symbols.size()>0)
    {
      for (goto_tracet::stepst::reverse_iterator it=
             trace.steps.rbegin();
           it!=trace.steps.rend();
           it++)
      {
        if (it->type==goto_trace_stept::ASSIGNMENT &&
            lhs_symbols.find(it->pc->code.op0())!=lhs_symbols.end())
        {
          const codet &code = to_code(it->pc->code);

          goto_programt::instructiont::labelst::const_iterator lit =
              find(it->pc->labels.begin(), it->pc->labels.end(),
                   irep_idt("VARIANT"));

          if (code.op1().get("statement")=="nondet" &&
              lit!=it->pc->labels.end())
          {
            if (out.good())
              out <<std::endl<<expr2c(code, ns)<<std::endl;
            nondet_counter++;
          }
          else
            find_symbols(code.op1(), lhs_symbols);
        }
      }
    }

    if (out.good())
      out << "Total nondet:" << nondet_counter << std::endl;

    return false;
  }
}

/*******************************************************************

 Function: symex_assertion_sumt::is_satisfiable

 Inputs:

 Outputs:

 Purpose: Checks if prepared formula is SAT

\*******************************************************************/

bool symex_assertion_sumt::is_satisfiable(
  decision_proceduret &decision_procedure,
  std::ostream &out)
{
  if (out.good())
    out <<std::endl<<"RESULT:"<<std::endl;

  fine_timet before, after;
  before=current_time();
  decision_proceduret::resultt r = decision_procedure.dec_solve();
  after=current_time();
  if (out.good())
    out << "SOLVER TIME: "<< time2string(after-before) << std::endl;

  solving_time += (after-before);
  global_satsolver_time += (after-before);

  // solve it
  switch (r)
  {
    case decision_proceduret::D_UNSATISFIABLE:
    {
      if (out.good())
        out<<"UNSAT - it holds!"<<std::endl;
      return false;
    }
    case decision_proceduret::D_SATISFIABLE:
    {
      if (out.good())
        out<<"SAT - doesn't hold"<<std::endl;
      return true;
    }

    default:
      throw "unexpected result from dec_solve()";
  }
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
  assert(!state.call_stack.empty());

  const goto_programt::instructiont &instruction=*state.source.pc;
  
  merge_gotos(state);

  // depth exceeded?
  {
    unsigned max_depth=atoi(options.get_option("depth").c_str());
    if(max_depth!=0 && state.depth>max_depth)
      state.guard.add(false_exprt());
    state.depth++;
  }

  // actually do instruction
  switch(instruction.type)
  {
  case SKIP:
    // really ignore
    state.source.pc++;
    break;

  case END_FUNCTION:

    store_return_value(state, get_current_deferred_function());
    store_modified_globals(state, get_current_deferred_function());
    dequeue_deferred_function(state);
    break;
  
  case LOCATION:
    target.location(state.guard, state.source);
    state.source.pc++;
    break;
  
  case GOTO:
    symex_goto(state);
    break;
    
  case ASSUME:
    if(!state.guard.is_false())
    {
      exprt tmp=instruction.guard;
      clean_expr(tmp, state, false);
      state.rename(tmp, ns);
      do_simplify(tmp);

      if(!tmp.is_true())
      {
        exprt tmp2=tmp;
        state.guard.guard_expr(tmp2);

        target.assumption(state.guard, tmp2, state.source);

        #if 0      
        // we also add it to the state guard
        state.guard.add(tmp);
        #endif
      }
    }

    state.source.pc++;
    break;

  case ASSERT:
    if(!state.guard.is_false())
      if(options.get_bool_option("assertions") ||
         !state.source.pc->location.get_bool("user-provided"))
      {
        // Is it the current assertion?
        if (current_assertion->get_location() == state.source.pc && (
                !options.get_bool_option("no-assert-grouping") ||
                get_current_deferred_function().assert_stack_match)) {
                  
          std::string msg=id2string(state.source.pc->location.get_comment());
          if(msg=="") msg="assertion";
          exprt tmp(instruction.guard);

          clean_expr(tmp, state, false);

          claim(tmp, msg, state);
        }
      }

    state.source.pc++;
    break;
    
  case RETURN:
    if(!state.guard.is_false())
      symex_return(state);

    state.source.pc++;
    break;

  case ASSIGN:
    if(!state.guard.is_false())
    {
      code_assignt deref_code=to_code_assign(instruction.code);

      clean_expr(deref_code.lhs(), state, true);
      clean_expr(deref_code.rhs(), state, false);

      basic_symext::symex_assign(state, deref_code);
    }

    state.source.pc++;
    break;

  case FUNCTION_CALL:
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
      target.assumption(state.guard, tmp, state.source);
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
        const deferred_functiont &deferred_function,
        irep_idt function_id) 
{
  bool first = deferred_functions.size() == 0;

  deferred_functions.push(deferred_function);
  deferred_functiont& fresh = deferred_functions.back();
  fresh.partition_id = equation.reserve_partition(
          deferred_function.callstart_symbol,
          deferred_function.callend_symbol,
          deferred_function.argument_symbols,
          deferred_function.out_arg_symbols,
          deferred_function.retval_symbol,
          deferred_function.returns_value,
          function_id);

  // Keep track of the stack match
  const deferred_functiont& parent = get_current_deferred_function();
  const call_stackt& stack = current_assertion->get_target_stack();

  if (first) {
    fresh.assert_stack_it = stack.begin();
    fresh.assert_stack_match = stack.size() == 1;
    return;
  }

  if (parent.assert_stack_it != stack.end()) 
  {
    const symbol_exprt& func_symb = to_symbol_expr(to_code_function_call(
            (*parent.assert_stack_it)->code).function());
    
    if (func_symb.get_identifier() == function_id) 
    {
      fresh.assert_stack_it = parent.assert_stack_it;
      fresh.assert_stack_it++;

      if (fresh.assert_stack_it == stack.end())
        fresh.assert_stack_match = true;
    
      return;
    }
  }
  fresh.assert_stack_it = stack.end();
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
  // Dequeue the previous deferred function
  deferred_functions.pop();

  if (deferred_functions.empty()) {
    // No more deferred functions, we are done
    current_summary_info = NULL;
    // Prepare the equation for further processing
    equation.prepare_partitions();
    return;
  }

  // Set the current summary info to one of the deferred functions
  deferred_functiont &deferred_function = deferred_functions.front();
  current_summary_info = &deferred_function.summary_info;
  const irep_idt& function_id = current_summary_info->get_function_id();

  std::cout << "Processing a deferred function: " << function_id << std::endl;

  // Select symex target equation to produce formulas into the corresponding
  // partition
  equation.select_partition(deferred_function.partition_id);

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

  // Setup temporary store for return value
  if (deferred_function.returns_value) {
    state.top().return_value = deferred_function.retval_tmp;
  } else {
    state.top().return_value.make_nil();
  }

  // Add an assumption of the function call_site symbol
  target.assumption(state.guard, deferred_function.callstart_symbol,
          state.source);

  // NOTE: In order to prevent name clashes with argument SSA versions,
  // we renew them all here.
  for (std::vector<symbol_exprt>::const_iterator it1 =
          deferred_function.argument_symbols.begin();
          it1 != deferred_function.argument_symbols.end();
          ++it1) {
    guardt guard;
    symbol_exprt lhs(state.get_original_name(it1->get_identifier()), ns.follow(it1->type()));
    symex_assign_symbol(state, lhs, *it1, guard, VISIBLE);
  }
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

  // find code in function map
  goto_functionst::function_mapt::const_iterator it =
    summarization_context.get_functions().function_map.find(identifier);

  if(it == summarization_context.get_functions().function_map.end())
    throw "failed to find `"+id2string(identifier)+"' in function_map";

  const goto_functionst::goto_functiont &goto_function=it->second;

  // Add parameters assignment
  bool old_cp = constant_propagation;
  constant_propagation = false;
  argument_assignments(goto_function.type, state, function_call.arguments());

  // Store the argument renamed symbols somewhere (so that we can use
  // them later, when processing the deferred function).
  mark_argument_symbols(goto_function.type, state, deferred_function);

  // TODO: Mark accessed global variables as well
  mark_accessed_global_symbols(identifier, state, deferred_function);
  
  // FIXME: We need to store the SSA_steps.size() here, so that 
  // SSA_exec_order is correctly ordered.
  // NOTE: The exec_order is not used now.

  if (function_call.lhs().is_not_nil()) {
    // Add return value assignment from a temporary variable and
    // store the temporary return value symbol somewhere (so that we can
    // use it later, when processing the deferred function).
    return_assignment_and_mark(goto_function.type, state, function_call.lhs(),
            deferred_function);
  } else {
    deferred_function.retval_symbol = symbol_exprt();
  }
  // FIXME: Add also new assignments to all modified global variables
  modified_globals_assignment_and_mark(identifier, state, deferred_function);
  
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
        deferred_functiont &deferred_function)
{
  const code_typet::argumentst &argument_types=function_type.arguments();

  for(code_typet::argumentst::const_iterator
      it=argument_types.begin();
      it!=argument_types.end();
      it++)
  {
    const code_typet::argumentt &argument=*it;
    const irep_idt &identifier=argument.get_identifier();

    symbol_exprt symbol(state.current_name(identifier), argument.type());

    deferred_function.argument_symbols.push_back(symbol);

#   ifdef DEBUG_PARTITIONING
    expr_pretty_print(std::cout << "Marking argument symbol: ", symbol);
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
    deferred_functiont &deferred_function) 
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
    const symbolt& symbol = ns.lookup(*it);
    symbol_exprt symb_ex(state.current_name(*it), symbol.type);
    
    deferred_function.argument_symbols.push_back(symb_ex);

#   ifdef DEBUG_PARTITIONING
    expr_pretty_print(std::cout << "Marking accessed global symbol: ", symb_ex);
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
    deferred_functiont &deferred_function)
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
    const symbolt& symbol = ns.lookup(*it);
    symbol_exprt symb_ex(get_new_symbol_version(*it, state), symbol.type);
    
    deferred_function.out_arg_symbols.push_back(symb_ex);

#   ifdef DEBUG_PARTITIONING
    expr_pretty_print(std::cout << "Marking modified global symbol: ", symb_ex);
#   endif
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
        const code_typet &function_type,
        statet &state,
        const exprt &lhs,
        deferred_functiont &deferred_function)
{
  assert(function_type.return_type().is_not_nil());

  const irep_idt &function_id = deferred_function.summary_info.get_function_id();
  const typet& type = function_type.return_type();
  std::string retval_symbol_id(
          "funfrog::" + function_id.as_string() + "::\\retval");
  std::string retval_tmp_id(
          "funfrog::" + function_id.as_string() + "::\\retval_tmp");
  symbol_exprt retval_symbol(get_new_symbol_version(retval_symbol_id, state),
          type);
  symbol_exprt retval_tmp(retval_tmp_id, type);

  add_symbol(retval_tmp_id, type, false);
  add_symbol(retval_symbol_id, type, true);

  code_assignt assignment(lhs, retval_symbol);
  assert( ns.follow(assignment.lhs().type()) ==
          ns.follow(type));

  bool old_cp = constant_propagation;
  constant_propagation = false;
  basic_symext::symex_assign(state, assignment);
  constant_propagation = old_cp;

# ifdef DEBUG_PARTITIONING
  expr_pretty_print(std::cout << "Marking return symbol: ", retval_symbol);
  expr_pretty_print(std::cout << "Marking return tmp symbol: ", retval_tmp);
# endif

  deferred_function.retval_symbol = retval_symbol;
  deferred_function.retval_tmp = retval_tmp;
  deferred_function.returns_value = true;
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
  
  for (std::vector<symbol_exprt>::const_iterator it = 
          deferred_function.out_arg_symbols.begin();
          it != deferred_function.out_arg_symbols.end();
          ++it) {
    
    symbol_exprt rhs(state.get_original_name(it->get_identifier()), 
            ns.follow(it->type()));
    code_assignt assignment(
            *it,
            rhs);
  
    assert( ns.follow(assignment.lhs().type()) ==
            ns.follow(assignment.rhs().type()));

    raw_assignment(state, assignment.lhs(), assignment.rhs(), ns, false);
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
  if (!deferred_function.returns_value)
    return;
  
  code_assignt assignment(
          deferred_function.retval_symbol,
          deferred_function.retval_tmp);
  
  assert( ns.follow(assignment.lhs().type()) ==
          ns.follow(assignment.rhs().type()));

  // Emit the assignment
  bool old_cp = constant_propagation;
  constant_propagation = false;
  raw_assignment(state, assignment.lhs(), assignment.rhs(), ns, false);
  constant_propagation = old_cp;
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
  const call_summaryt &call_summary =
          current_summary_info->get_call_sites().find(state.source.pc)->second;
  deferred_functiont deferred_function(call_summary.get_summary_info());
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
  if(!goto_function.body_available)
  {
    no_body(function_id);

    if(function_call.lhs().is_not_nil())
    {
      exprt rhs = exprt("nondet_symbol", function_call.lhs().type());
      rhs.set(ID_identifier, "symex::" + i2string(nondet_count++));
      rhs.location() = function_call.location();
      code_assignt code(function_call.lhs(), rhs);
      basic_symext::symex(state, code);
    }

    state.source.pc++;
    return;
  }


  // Assign function parameters and return value
  assign_function_arguments(state, function_call, deferred_function);

  switch (call_summary.get_precision()) {
  case call_summaryt::NONDET:
    havoc_function_call(deferred_function, state, function_id);
    break;
  case call_summaryt::SUMMARY:
    summarize_function_call(deferred_function, state, function_id);
    break;
  case call_summaryt::INLINE:
    inline_function_call(deferred_function, state, function_id);
    break;
  default:
    assert(false);
    break;
  }
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
  std::cout << "*** SUMMARY abstraction used for function: " <<
          function_id << std::endl;

  produce_callsite_symbols(deferred_function, state, function_id);
  produce_callend_assumption(deferred_function, state);

  std::cout << "Substituting interpolant" << std::endl;

  partition_idt partition_id = equation.reserve_partition(
          deferred_function.callstart_symbol,
          deferred_function.callend_symbol,
          deferred_function.argument_symbols,
          deferred_function.out_arg_symbols,
          deferred_function.retval_symbol,
          deferred_function.returns_value,
          function_id);
  equation.fill_summary_partition(partition_id,
          &summarization_context.get_summaries(function_id));
}

/*******************************************************************

 Function: symex_assertion_sumt::summarize_function_call

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
  std::cout << "*** INLINING function: " <<
          function_id << std::endl;

  produce_callsite_symbols(deferred_function, state, function_id);
  produce_callend_assumption(deferred_function, state);

  defer_function(deferred_function, function_id);
}
/*******************************************************************

 Function: symex_assertion_sumt::summarize_function_call

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

  // FIXME: We need some static analysis of the function for this
  std::cout << "*** NONDET abstraction used for function: " <<
          function_id << std::endl;

  produce_callsite_symbols(deferred_function, state, function_id);
  produce_callend_assumption(deferred_function, state);
}

/*******************************************************************

 Function: symex_assertion_sumt::produce_callsite_symbols

 Inputs:

 Outputs:

 Purpose: Creates new call site (start & end) symbols for the given
 deferred function

\*******************************************************************/
void symex_assertion_sumt::produce_callsite_symbols(
        deferred_functiont& deferred_function,
        statet& state,
        const irep_idt& function_id)
{
  irep_idt callstart_id = "funfrog::" + function_id.as_string() +
          "::\\callstart_symbol";
  irep_idt callend_id = "funfrog::" + function_id.as_string() +
          "::\\callend_symbol";

  deferred_function.callstart_symbol.set_identifier(
          get_new_symbol_version(callstart_id, state));
  deferred_function.callend_symbol.set_identifier(
          get_new_symbol_version(callend_id, state));

  add_symbol(callstart_id, typet(ID_bool), true);
  add_symbol(callend_id, typet(ID_bool), true);
}

/*******************************************************************

 Function: symex_assertion_sumt::produce_callsite_symbols

 Inputs:

 Outputs:

 Purpose: Inserts assumption that a given call ended (i.e., an assumption of
 the callend symbol)

\*******************************************************************/
void symex_assertion_sumt::produce_callend_assumption(
        const deferred_functiont& deferred_function, statet& state)
{
  exprt tmp(deferred_function.callend_symbol);
  state.guard.guard_expr(tmp);
  target.assumption(state.guard, tmp, state.source);
}


/*******************************************************************

 Function: symex_assertion_sumt::get_new_symbol_version

 Inputs:

 Outputs:

 Purpose: Helper function for renaming of an identifier without
 assigning to it. Constant propagation is stopped for the given symbol.

\*******************************************************************/
std::string symex_assertion_sumt::get_new_symbol_version(
        const irep_idt& identifier,
        statet &state)
{
  //--8<--- Taken from goto_symex_statt::assignment()
  // identifier should be l0 or l1, make sure it's l1
  const std::string l1_identifier=state.top().level1(identifier);
  // do the l2 renaming
  statet::level2t::valuet &entry=state.level2.current_names[l1_identifier];
  entry.count++;
  // Break constant propagation for this new symbol
  entry.constant.make_nil();
  state.level2.rename(l1_identifier, entry.count);
  return state.level2.name(l1_identifier, entry.count);
  //--8<---
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
        const namespacet &ns,
        bool record_value)
{
  symbol_exprt rhs_symbol = to_symbol_expr(rhs);
  rhs_symbol.set(ID_identifier, state.current_name(rhs_symbol.get_identifier()));

  // FIXME: Check that this does not mess (too much) with the value sets
  // and constant propagation
  //--8<--- Taken from goto_symex_statt::assignment()
  assert(lhs.id()==ID_symbol);

  // the type might need renaming
  state.rename(lhs.type(), ns);

  const irep_idt &identifier=
    lhs.get(ID_identifier);

  // identifier should be l0 or l1, make sure it's l1

  const std::string l1_identifier=state.top().level1(identifier);

  // do the l2 renaming
  statet::level2t::valuet &entry=state.level2.current_names[l1_identifier];

  // We do not want the new version!
  // OLD:
  //
  // entry.count++;
  //
  // state.level2.rename(l1_identifier, entry.count);
  //
  // lhs.set(ID_identifier, level2.name(l1_identifier, entry.count));

  if(record_value)
  {
    // for constant propagation

    if(state.constant_propagation(rhs_symbol))
      entry.constant=rhs_symbol;
    else
      entry.constant.make_nil();
  }
  else
    entry.constant.make_nil();

  // update value sets
  exprt l1_rhs(rhs_symbol);
  state.level2.get_original_name(l1_rhs);
  exprt l1_lhs(lhs);
  state.level2.get_original_name(l1_lhs);

  state.value_set.assign(l1_lhs, l1_rhs, ns);
  //--8<---

  guardt empty_guard;

  target.assignment(
    empty_guard,
    lhs, l1_lhs,
    rhs_symbol,
    state.source,
    symex_targett::STATE);
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
  // FIXME: The variables get cumulated in level2 cache,
  // we need to get rid of the old ones...
  
  // go over all variables to see what changed
  for(goto_symex_statet::level2t::current_namest::const_iterator
      it = goto_state.level2.current_names.begin();
      it != goto_state.level2.current_names.end();
      ++it)
  {
    goto_symex_statet::level2t::current_namest::const_iterator d_it =
            dest_state.level2.current_names.find(it->first);
            
    if(d_it == dest_state.level2.current_names.end()) {
      // Only present in the new state. No assignment needed, just reuse the 
      // count
      dest_state.level2.current_names[it->first] = it->second;
      continue;
    }
    
    if (it->second.count == d_it->second.count)
      continue; // not at all changed

    irep_idt original_identifier = dest_state.get_original_name(it->first);

    if (is_dead_identifier(original_identifier))
      continue;

    // changed!
    const symbolt &symbol=ns.lookup(original_identifier);

    typet type(symbol.type);

    // type may need renaming
    dest_state.rename(type, ns);

    exprt rhs;

    if(dest_state.guard.is_false())
    {
      rhs=symbol_exprt(dest_state.current_name(goto_state, symbol.name), type);
    }
    else if(goto_state.guard.is_false())
    {
      rhs=symbol_exprt(dest_state.current_name(symbol.name), type);
    }
    else
    {
      guardt tmp_guard(goto_state.guard);

      // this gets the diff between the guards
      tmp_guard-=dest_state.guard;

      rhs=if_exprt();
      rhs.type()=type;
      rhs.op0()=tmp_guard.as_expr();
      rhs.op1()=symbol_exprt(dest_state.current_name(goto_state, symbol.name), type);
      rhs.op2()=symbol_exprt(dest_state.current_name(symbol.name), type);
    }

    exprt lhs(symbol_expr(symbol));
    exprt new_lhs(lhs);

    dest_state.assignment(new_lhs, rhs, ns, false);

    guardt true_guard;

    target.assignment(
      true_guard,
      new_lhs, lhs,
      rhs,
      dest_state.source,
      symex_targett::HIDDEN);
  }
  
  /*
  // go over all variables to see what changed
  std::set<irep_idt> variables;

  goto_state.level2.get_variables(variables);
  dest_state.level2.get_variables(variables);

  for(std::set<irep_idt>::const_iterator
      it=variables.begin();
      it!=variables.end();
      ++it)
  {
    irep_idt original_identifier = dest_state.get_original_name(*it);

    if (is_dead_identifier(original_identifier))
      continue;

    if(goto_state.level2.current_number(*it)==
       dest_state.level2.current_number(*it))
      continue; // not at all changed

    // changed!
    const symbolt &symbol=ns.lookup(original_identifier);

    typet type(symbol.type);

    // type may need renaming
    dest_state.rename(type, ns);

    exprt rhs;

    if(dest_state.guard.is_false())
    {
      rhs=symbol_exprt(dest_state.current_name(goto_state, symbol.name), type);
    }
    else if(goto_state.guard.is_false())
    {
      rhs=symbol_exprt(dest_state.current_name(symbol.name), type);
    }
    else
    {
      guardt tmp_guard(goto_state.guard);

      // this gets the diff between the guards
      tmp_guard-=dest_state.guard;

      rhs=if_exprt();
      rhs.type()=type;
      rhs.op0()=tmp_guard.as_expr();
      rhs.op1()=symbol_exprt(dest_state.current_name(goto_state, symbol.name), type);
      rhs.op2()=symbol_exprt(dest_state.current_name(symbol.name), type);
    }

    exprt lhs(symbol_expr(symbol));
    exprt new_lhs(lhs);

    dest_state.assignment(new_lhs, rhs, ns, false);

    guardt true_guard;

    target.assignment(
      true_guard,
      new_lhs, lhs,
      rhs,
      dest_state.source,
      symex_targett::HIDDEN);
  }
  */
}
