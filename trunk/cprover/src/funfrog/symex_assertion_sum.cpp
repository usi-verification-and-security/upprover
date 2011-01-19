/*******************************************************************

 Module: Symbolic execution and deciding of a given goto-program
 using and generating function summaries. Based on symex_asserion.h

 Author: Ondrej Sery

\*******************************************************************/
    
#include <memory>

#include <goto-symex/build_goto_trace.h>
#include <find_symbols.h>
#include <ansi-c/expr2c.h>
#include <time_stopping.h>
#include <solvers/sat/satcheck.h>
#include <solvers/smt1/smt1_dec.h>

#include "symex_assertion_sum.h"
#include "../loopfrog/memstat.h"

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
         it != last && it != goto_program.instructions.end();
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

//  state.value_set = value_sets;
  for(state.source.pc = goto_program.instructions.begin();
      state.source.pc != last && 
      state.source.pc != goto_program.instructions.end();
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

  std::auto_ptr<satcheckt> sat_solver;
  std::auto_ptr<prop_convt> deciderp;

  if (use_smt)
  {
    deciderp = std::auto_ptr<prop_convt>(
        new smt1_dect(ns, "loop.smt", "", "QF_AUFBV", smt1_dect::BOOLECTOR));
  }
  else
  {
    sat_solver = std::auto_ptr<satcheckt>(new satcheckt());
    bv_pointerst *p= new bv_pointerst(ns, *sat_solver);
    p->unbounded_array = bv_pointerst::U_AUTO;
    deciderp=std::auto_ptr<prop_convt>(p);
  }

  prop_convt &decider=*deciderp;

  decider.set_message_handler(message_handler);
  decider.set_verbosity(10);

  if(remaining_claims!=0)
  {
    before=current_time();
    slice(equation);
    after=current_time();

    if (out.good())
      out << "SLICER TIME: "<< time2string(after-before) << std::endl;

    fine_timet before,after;
    before=current_time();
    equation.convert(decider);
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
    symex_end_of_function(state);
    state.source.pc++;
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

      if(deref_code.lhs().is_not_nil())
        clean_expr(deref_code.lhs(), state, true);

      clean_expr(deref_code.function(), state, false);

      Forall_expr(it, deref_code.arguments())
        clean_expr(*it, state, false);
    
      symex_function_call(goto_functions, state, deref_code);
    }
    else
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
