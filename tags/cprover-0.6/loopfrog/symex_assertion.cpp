/*******************************************************************

 Module: Symbolic execution and deciding of a given goto-program

 Author: Aliaksei Tsitovich,
         CM Wintersteiger

\*******************************************************************/

#include <memory>

#include <goto-symex/build_goto_trace.h>
#include <find_symbols.h>
#include <ansi-c/expr2c.h>
#include <time_stopping.h>
#include <pointer-analysis/value_set_analysis.h>
#include <solvers/sat/satcheck.h>
#include <solvers/smt1/smt1_dec.h>

#include "symex_assertion.h"
#include "localized_inlining.h"
#include "memstat.h"

fine_timet global_satsolver_time;
fine_timet global_sat_conversion_time;

/*******************************************************************

 Function: last_assertion_holds

 Inputs:

 Outputs:

 Purpose: Checks if the last assertion of the GP holds

\*******************************************************************/

bool last_assertion_holds(
  const contextt &context,
  const value_setst &value_sets,
  goto_programt::const_targett &head,
  const goto_programt &goto_program,
  std::ostream &out,
  unsigned long &max_memory_used,
  bool use_smt)
{
  contextt temp_context;
  namespacet ns(context, temp_context);
  symex_target_equationt equation(ns);
  symex_assertiont symex(value_sets, head, ns, temp_context, equation);
  return symex.last_assertion_holds(goto_program, out,
                                    max_memory_used, use_smt);
}

/*******************************************************************

 Function: symex_assertiont::last_assertion_holds

 Inputs:

 Outputs:

 Purpose: Checks if the last assertion of the GP holds

\*******************************************************************/

bool symex_assertiont::last_assertion_holds(
  const goto_programt &goto_program,
  std::ostream &out,
  unsigned long &max_memory_used,
  bool use_smt)
{
  assert(!goto_program.empty() &&
         goto_program.instructions.rbegin()->type==ASSERT);

  goto_programt::const_targett last=goto_program.instructions.end(); last--;

  return assertion_holds(goto_program, last, out, max_memory_used, use_smt);
}

/*******************************************************************

 Function: assertion_holds

 Inputs:

 Outputs:

 Purpose: Checks if the given assertion of the GP holds (without value sets)

\*******************************************************************/

bool assertion_holds(
  const contextt &context,
  const goto_programt &goto_program,
  goto_programt::const_targett &assertion,
  std::ostream &out,
  unsigned long &max_memory_used,
  bool use_smt)
{
  contextt temp_context;
  namespacet ns(context, temp_context);
  symex_target_equationt equation(ns);  
  goto_programt::const_targett first = goto_program.instructions.begin();
  symex_assertiont symex(value_set_analysist(ns), 
                         first, 
                         ns, temp_context, equation);
  return symex.assertion_holds(goto_program, assertion, out,
                               max_memory_used, use_smt);
}

/*******************************************************************

 Function: assertion_holds

 Inputs:

 Outputs:

 Purpose: Checks if the given assertion of the GP holds

\*******************************************************************/

bool assertion_holds(
  const contextt &context,
  const value_setst &value_sets,
  goto_programt::const_targett &head,
  const goto_programt &goto_program,
  goto_programt::const_targett &assertion,
  std::ostream &out,
  unsigned long &max_memory_used,
  bool use_smt)
{
  contextt temp_context;
  namespacet ns(context, temp_context);
  symex_target_equationt equation(ns);
  symex_assertiont symex(value_sets, head, ns, temp_context, equation);
  return symex.assertion_holds(goto_program, assertion, out,
                               max_memory_used, use_smt);
}

/*******************************************************************

 Function: symex_assertiont::assertion_holds

 Inputs:

 Outputs:

 Purpose: Checks if the given assertion of the GP holds

\*******************************************************************/

bool symex_assertiont::assertion_holds(
  const goto_programt &goto_program,
  goto_programt::const_targett &assertion,
  std::ostream &out,
  unsigned long &max_memory_used,
  bool use_smt)
{
  stream_message_handlert message_handler(out);

  // these are quick...
  if(assertion->guard.is_true())
  {
    out << std::endl << "ASSERTION IS TRUE" << std::endl;
    return true;
  }

  goto_programt::const_targett last = assertion; last++;

  // Print out the initial goto-program
  if(out.good())
  {
    out << std::endl << "GOTO-PROGRAM:" << std::endl;
    for (goto_programt::instructionst::const_iterator it=
           goto_program.instructions.begin();
         it!=last;
         it++)
      goto_program.output_instruction(ns, "", out, it);
  }

  #if 1
  // sanity check
  forall_goto_program_instructions(it, goto_program)
    assert(!it->is_backwards_goto() && it->type!=FUNCTION_CALL);
  #endif

  #if 0
  // Sanity Check,
  // warning: this check only works with assume-guarantee reasoning off.
  for(goto_programt::const_targett it=goto_program.instructions.begin();
      it!=assertion;
      it++)
    assert(it->type!=ASSERT);
  #endif

  // Proceed with symbolic execution
  fine_timet before, after;
  before=current_time();
  
  goto_symext::statet state; 
  
//  state.value_set = value_sets;
  goto_functionst temp;
  for(state.source.pc=goto_program.instructions.begin();
      state.source.pc!=last;
      )
  {
//    goto_program.output_instruction(ns, "", std::cout, state.source.pc);
    symex_step(temp, state);
//    state.value_set.output(ns, std::cout);
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
    find_symbols(assertion->guard, lhs_symbols);

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

 Function: symex_assertiont::is_satisfiable

 Inputs:

 Outputs:

 Purpose: Checks if prepared formula is SAT

\*******************************************************************/

bool symex_assertiont::is_satisfiable(
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

/*******************************************************************

 Function: symex_assertiont::convert

 Inputs:

 Outputs:

 Purpose: Converts the equation to CNF (obsolete)

\*******************************************************************/

//void symex_assertiont::convert(
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

 Function: symex_assertiont::equation_holds

 Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

bool symex_assertiont::equation_holds(
  symex_target_equationt &target,
  std::ostream &out,
  unsigned long &max_memory_used,
  bool use_smt)
{
  stream_message_handlert message_handler(out);
    
  fine_timet before, after;
  bool sat=false;

  satcheckt satcheck;
  bv_pointerst decider(ns, satcheck);

  decider.set_message_handler(message_handler);
  decider.set_verbosity(10);
  
  if(out.good())
  {
    out << std::endl << "EQUATION:" << std::endl; 
    target.output(out); 
  }

  // Decides the equation
  decider.unbounded_array = bv_pointerst::U_AUTO;
  
  before=current_time();
  target.convert(decider);
  after=current_time();
  global_sat_conversion_time += (after-before);

  sat = is_satisfiable(decider, out);

  if (use_smt)
  {
    //stub for SMT solver
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
    build_goto_trace(target, decider, trace);
    if (out.good())
      show_goto_trace(out, ns, trace);

    return false;
  }
}

/*******************************************************************

 Function: symex_assertiont::to_equation

 Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void symex_assertiont::to_equation(
  const contextt &context,
  contextt &temp_context,
  const value_setst &value_sets,
  goto_programt::const_targett &head,
  const goto_programt &goto_program,
  goto_programt::const_targett &assertion,
  symex_target_equationt &target,
  std::ostream &out,
  unsigned long &max_memory_used,
  bool use_smt)
{
  fine_timet before, after;  

  namespacet ns(context, temp_context);
  
  goto_symext goto_symex(ns, temp_context, target);
  goto_symext::statet state;
  goto_programt::const_targett last = assertion; last++;
  
  before=current_time();
  goto_functionst temp;
  for(state.source.pc=goto_program.instructions.begin();
      state.source.pc!=last;
      )
  {
//    goto_program.output_instruction(ns, "", std::cout, state.source.pc);
    symex_step(temp, state);
  }
  after=current_time();

  if(out.good())
    out << "SYMEX TIME: "<< time2string(after-before) << std::endl;
}

/*******************************************************************

 Function: symex_assertiont::slice_equation

 Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void symex_assertiont::slice_equation(
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
