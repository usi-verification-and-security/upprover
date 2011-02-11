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

#include "symex_assertion_sum.h"
#include "expr_pretty_print.h"
#include "solvers/satcheck_opensmt.h"

fine_timet global_satsolver_time;
fine_timet global_sat_conversion_time;


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
  bool use_smt)
{
  stream_message_handlert message_handler(out);

  // these are quick...
  if(assertion.get_location()->guard.is_true())
  {
    out << std::endl << "ASSERTION IS TRUE" << std::endl;
    return true;
  }

  goto_programt::const_targett last = assertion.get_location(); last++;

  // Print out the initial goto-program
  // FIXME: Does not print all the functions recursively --> it is useless
  if(out.good())
  {
    out << std::endl << "GOTO-PROGRAM:" << std::endl;
    for (goto_programt::instructionst::const_iterator it=
           goto_program.instructions.begin();
         /*it != last &&*/ it != goto_program.instructions.end();
         it++)
      goto_program.output_instruction(ns, "", out, it);
  }

# ifndef NDEBUG
  // sanity check, we expect loop-free programs, this should be done for all 
  // functions
  forall_goto_program_instructions(it, goto_program)
    assert(!it->is_backwards_goto());
  forall_goto_functions(it, summarization_context.functions)
    forall_goto_program_instructions(it2, it->second.body)
      assert(!it2->is_backwards_goto());
# endif

  // Proceed with symbolic execution
  fine_timet before, after;
  before=current_time();

  goto_symext::statet state;
  // Prepare for the pc++ after returning from the last END_FUNCTION
  state.top().calling_location = --goto_program.instructions.end();

  // Prepare the partitions and deferred functions
  defer_function(deferred_functiont(summary_info));
  equation.select_partition(deferred_functions.front().partition_id);

  // Old: ??? state.value_set = value_sets;

  // FIXME: If we care only about a single assertion, we should stop 
  // as soon as it is reached.
  for(state.source.pc = goto_program.instructions.begin();
      has_more_steps(state);
      )
  {
    goto_program.output_instruction(ns, "", std::cout, state.source.pc);
    symex_step(summarization_context.functions, state);
    // state.value_set.output(ns, std::cout);
  }
  after=current_time();

  if(out.good())
    out << "SYMEX TIME: "<< time2string(after-before) << std::endl;

  bool sat=false;

  std::auto_ptr<propt> sat_solver;
  std::auto_ptr<prop_convt> deciderp;
  interpolating_solvert* interpolator = NULL;

  if (use_smt)
  {
    deciderp = std::auto_ptr<prop_convt>(
        new smt1_dect(ns, "loop.smt", "", "QF_AUFBV", smt1_dect::BOOLECTOR));
  }
  else
  {
    // sat_solver.reset(new satcheckt());
    satcheck_opensmtt* opensmt = new satcheck_opensmtt();
    interpolator = opensmt;
    sat_solver.reset(opensmt);
    bv_pointerst *p= new bv_pointerst(ns, *sat_solver);
    p->unbounded_array = bv_pointerst::U_AUTO;
    deciderp.reset(p);
  }

  prop_convt &decider=*deciderp;

  decider.set_message_handler(message_handler);
  decider.set_verbosity(10);

  if(remaining_claims!=0)
  {
    before=current_time();
    // FIXME: Slicer does not expect deferring of function inlining
    // and removes also important parts of the code.
    // slice(equation);
    after=current_time();

    if (out.good())
      out << "SLICER TIME: "<< time2string(after-before) << std::endl;

    fine_timet before,after;
    before=current_time();
    equation.convert(decider, *interpolator);
    after=current_time();
    global_sat_conversion_time += (after-before);

    // Decides the equation
    sat = is_satisfiable(decider, out);
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
        std::string msg=id2string(state.source.pc->location.get_comment());
        if(msg=="") msg="assertion";
        exprt tmp(instruction.guard);

        clean_expr(tmp, state, false);

        claim(tmp, msg, state);
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

      // Process the function call according to the call_sumamry
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

 Function: symex_assertion_sumt::convert

 Inputs:

 Outputs:

 Purpose: Converts the equation to CNF (obsolete)

\*******************************************************************/

//void symex_assertion_sumt::convert(
//  namespacet &ns,
//  prop_convt &prop_conv,
//  symex_target_equationt &equation,
//  symex_target_equationt::statest::iterator last,
//  std::ostream &out)
//{
//  symex_target_equationt::statest::iterator end = last;
//  end++;
//
//  if (out.good())
//    out<<std::endl<<"CONSTRAINTS:"<<std::endl;
//
//  for (symex_target_equationt::statest::iterator it=equation.states.begin();
//      it!=end; it++)
//  {
//    it->guard_literal=const_literal(true);
//    switch (it->type)
//    {
//      case goto_trace_stept::ASSIGNMENT:
//      case goto_trace_stept::ASSUME:
//      {
//        exprt tmp(it->cond);
//        ::base_type(tmp, ns);
//        prop_conv.set_to_true(tmp);
//        it->cond_literal=const_literal(true);
//
//        if(out.good())
//        out << "CONSTRAINT: " << from_expr(ns, "", tmp) << std::endl;
//      }
//      break;
//
//      case goto_trace_stept::ASSERT:
//      {
//        if (it!=last)
//        {
//          exprt tmp(it->cond);
//          ::base_type(tmp, ns);
//          prop_conv.set_to_true(tmp);
//          it->cond_literal=const_literal(true);
//          if(out.good())
//          out << "CONSTRAINT: " << from_expr(ns, "", tmp) << std::endl;
//        }
//        else
//        {
//          exprt tmp(it->cond);
//          ::base_type(tmp, ns);
//          prop_conv.set_to_false(tmp);
//          it->cond_literal=const_literal(false);
//          if(out.good())
//          out << "CONSTRAINT: NOT " << from_expr(ns, "", tmp) << std::endl;
//        }
//      }
//      break;
//
//      case goto_trace_stept::LOCATION: break;
//
//      default:
//      assert(false);
//    }
//  }
//}

/*******************************************************************

 Function: symex_assertion_sumt::slice_equation

 Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void symex_assertion_sumt::slice_equation(
  const contextt &context,
  contextt &temp_context,
  symex_target_equationt &target,
  std::ostream &out) const
{
  fine_timet before, after;

  namespacet ns(context, temp_context);

  before=current_time();
  goto_symext goto_symex(ns, temp_context, target);
  slice(target);
  after=current_time();

  if (out.good())
    out << "SLICER TIME: "<< time2string(after-before) << std::endl;
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

  std::cout << "Processing a deferred function: " << function_id;

  // Select symex target equation to produce formulas into the corresponding
  // partition
  equation.select_partition(deferred_function.partition_id);

  // Prepare (and empty) the current state
  state.guard.make_true();

  // Set pc to function entry point
  // NOTE: Here, we expect having the function body available
  const goto_programt& body = 
    summarization_context.functions.function_map.at(function_id).body;
  state.source.pc = body.instructions.begin();

  // Setup temporary store for return value
  if (deferred_function.returns_value) {
    state.top().return_value = deferred_function.retval_tmp;
  }

  // Add an assumption of the function call_site symbol
  target.assumption(state.guard, deferred_function.callstart_symbol,
          state.source);
}

/*******************************************************************

 Function: symex_assertion_sumt::assign_function_arguments

 Inputs:

 Outputs:

 Purpose: Assigns function arguments to new symbols, also makes
 assignement of the new symbol of return value to the lhs of
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
    summarization_context.functions.function_map.find(identifier);

  if(it == summarization_context.functions.function_map.end())
    throw "failed to find `"+id2string(identifier)+"' in function_map";

  const goto_functionst::goto_functiont &goto_function=it->second;

  // Add parameters assignment
  argument_assignments(goto_function.type, state, function_call.arguments());
  // Store the argument renamed symbols somewhere (so that we can use
  // them later, when processing the deferred function).
  mark_argument_symbols(goto_function.type, state, deferred_function);

  if (function_call.lhs().is_not_nil()) {
    // Add return value assignment from a temporary variable and
    // store the temporary return value symbol somewhere (so that we can
    // use it later, when processing the deferred function).
    return_assignment_and_mark(goto_function.type, state, function_call.lhs(),
            deferred_function);
  }
  // FIXME: Add also new assignments to all modified global variables
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

    expr_pretty_print(std::cout << "Marking argument symbol: ", symbol);
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
  std::string retval_symbol_id(
          "funfrog::" + function_id.as_string() + "::\\retval");
  std::string retval_tmp_id(
          "funfrog::" + function_id.as_string() + "::\\retval_tmp");
  symbol_exprt retval_symbol(
          get_new_symbol_version(retval_symbol_id, state),
          function_type.return_type());
  symbol_exprt retval_tmp(
          retval_tmp_id,
          function_type.return_type());

  code_assignt assignment(lhs, retval_symbol);
  assert( ns.follow(assignment.lhs().type()) ==
          ns.follow(assignment.rhs().type()));

  basic_symext::symex_assign(state, assignment);

  deferred_function.retval_symbol = retval_symbol;
  deferred_function.retval_tmp = retval_tmp;
  deferred_function.returns_value = true;
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
  raw_assignment(state, assignment.lhs(), assignment.rhs(), ns, false);
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

  // Clean expressions in the arguments, function name, and lhs (if any)
  if (function_call.lhs().is_not_nil())
    clean_expr(function_call.lhs(), state, true);

  clean_expr(function_call.function(), state, false);

  Forall_expr(it, function_call.arguments())
  clean_expr(*it, state, false);

  // Assign function parameters and return value
  assign_function_arguments(state, function_call, deferred_function);

  switch (call_summary.get_precision()) {
  case call_summaryt::NONDET:
    // We should treat the function as nondeterministic, havocing
    // all data it touches.

    // FIXME: We need some static analysis of the function for this
    std::cout << "*** NONDET abstraction used for function: " <<
            function_id << std::endl;
    break;
  case call_summaryt::SUMMARY:
    // We should use an already computed summary as an abstraction
    // of the function body

    // FIXME: Implement this
    std::cout << "*** SUMMARY abstraction used for function: " <<
            function_id << std::endl;
    break;
  case call_summaryt::INLINE:
  {
    // We should inline the body --> defer this for later

    std::cout << "*** INLINING function: " <<
            function_id << std::endl;

    produce_callsite_symbols(deferred_function, state, function_id);

    // Add assumption for the function call end symbol
    exprt tmp(deferred_function.callend_symbol);

    state.guard.guard_expr(tmp);
    target.assumption(state.guard, tmp, state.source);

    defer_function(deferred_function);
    break;
  }
  default:
    assert(false);
    break;
  }
}
/*******************************************************************

 Function: symex_assertion_sumt::handle_function_call

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
  deferred_function.callstart_symbol.set_identifier(
          get_new_symbol_version("funfrog::" + function_id.as_string() +
          "::\\callstart_symbol", state));
  deferred_function.callend_symbol.set_identifier(
          get_new_symbol_version("funfrog::" + function_id.as_string() +
          "::\\callend_symbol", state));
}

/*******************************************************************

 Function: symex_assertion_sumt::get_new_symbol_version

 Inputs:

 Outputs:

 Purpose: Helper function for renaming of an identifier without
 assigning to it.

\*******************************************************************/
std::string symex_assertion_sumt::get_new_symbol_version(
        const std::string &identifier,
        statet &state)
{
  //--8<--- Taken from goto_symex_statt::assignment()
  // identifier should be l0 or l1, make sure it's l1
  const std::string l1_identifier=state.top().level1(identifier);
  // do the l2 renaming
  statet::level2t::valuet &entry=state.level2.current_names[l1_identifier];
  entry.count++;
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