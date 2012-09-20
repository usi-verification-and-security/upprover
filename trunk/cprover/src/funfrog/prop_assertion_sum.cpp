/*******************************************************************

 Module: Propositional encoding of an SSA-form,
         And checking of its satisfiability

 Author: Ondrej Sery

\*******************************************************************/

#include <goto-symex/build_goto_trace.h>
#include <goto-symex/xml_goto_trace.h>
#include <find_symbols.h>
#include <ansi-c/expr2c.h>
#include <time_stopping.h>
#include <loopfrog/memstat.h>
#include <ui_message.h>
#include "prop_assertion_sum.h"

#define USE_EXEC_ORDER_ERROR_TRACE

fine_timet global_satsolver_time;
fine_timet global_sat_conversion_time;

/*******************************************************************

 Function: prop_assertion_sumt::assertion_holds

 Inputs:

 Outputs:

 Purpose: Checks if the given assertion of the GP holds

\*******************************************************************/

bool prop_assertion_sumt::assertion_holds(const assertion_infot &assertion, const namespacet &ns, prop_convt& decider, interpolating_solvert& interpolator)
{
  //stream_message_handlert message_handler(out);

  bool sat=false;

  decider.set_message_handler(message_handler);
  decider.set_verbosity(10);

  fine_timet before, after;
  before=current_time();
  equation.convert(decider, interpolator);
  after=current_time();
  global_sat_conversion_time += (after-before);

  status(std::string("CONVERSION TIME: ") + time2string(after-before));

  // Decides the equation
  sat = is_satisfiable(decider);

  unsigned long this_mem = current_memory();
  if (this_mem > max_memory_used)
    max_memory_used = this_mem;

  if (!sat)
  {
	  status("ASSERTION IS TRUE");
    return true;
  }
  else
  {
    /* error_trace(decider, ns);
    //std::cout << std::endl << "NONDET assigns:" << std::endl;

    unsigned int nondet_counter=0;
    std::set<exprt> lhs_symbols;
    if (!assertion.is_all_assert())
      find_symbols(assertion.get_location()->guard, lhs_symbols);

    if (lhs_symbols.size()>0)
    {
      for (goto_tracet::stepst::reverse_iterator it=
             trace.steps.rbegin();
           it!=trace.steps.rend();
           it++)
      {
        // FIXME: Work around for a broken error_trace
        if (it->type==goto_trace_stept::ASSIGNMENT &&
                !it->pc->code.has_operands())
          continue;
        
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
            // std::cout <<std::endl<<expr2c(code, ns)<<std::endl;
            nondet_counter++;
          }
          else
            find_symbols(code.op1(), lhs_symbols);
        }
      }
    }

    //std::cout << "Total nondet:" << nondet_counter << std::endl;
    */
    return false;
  }
}

/*******************************************************************

 Function: prop_assertion_sumt::is_satisfiable

 Inputs:

 Outputs:

 Purpose: Checks if prepared formula is SAT

\*******************************************************************/

bool prop_assertion_sumt::is_satisfiable(
  decision_proceduret &decision_procedure)
{
  status("RESULT");
  fine_timet before, after;
  before=current_time();
  decision_proceduret::resultt r = decision_procedure.dec_solve();
  after=current_time();
  status(std::string("SOLVER TIME: ") + time2string(after-before));

  solving_time = (after-before);
  global_satsolver_time += (after-before);

  // solve it
  switch (r)
  {
    case decision_proceduret::D_UNSATISFIABLE:
    {
      status("UNSAT - it holds!");
      return false;
    }
    case decision_proceduret::D_SATISFIABLE:
    {
      status("SAT - doesn't hold");
      return true;
    }

    default:
      throw "unexpected result from dec_solve()";
  }
}

// Copied from build_goto_tarce.cpp
void build_exec_order_goto_trace(
  partitioning_target_equationt &target,
  const prop_convt &prop_conv,
  goto_tracet &goto_trace)
{
  unsigned step_nr=0;
  
  const SSA_steps_orderingt& SSA_steps = target.get_steps_exec_order();
  
  for(SSA_steps_orderingt::const_iterator
      it=SSA_steps.begin();
      it!=SSA_steps.end();
      it++)
  {
    const symex_target_equationt::SSA_stept &SSA_step=**it;
    
    if(prop_conv.prop.l_get(SSA_step.guard_literal)!=tvt(true))
      continue;

    if(SSA_step.is_assignment() &&
       SSA_step.assignment_type==symex_target_equationt::HIDDEN)
      continue;

    step_nr++;
    
    goto_trace.steps.push_back(goto_trace_stept());    
    goto_trace_stept &goto_trace_step=goto_trace.steps.back();
    
    goto_trace_step.thread_nr=SSA_step.source.thread_nr;
    goto_trace_step.lhs=SSA_step.lhs;
    goto_trace_step.rhs=SSA_step.rhs;
    goto_trace_step.pc=SSA_step.source.pc;
    goto_trace_step.comment=SSA_step.comment;
    goto_trace_step.original_lhs=SSA_step.original_lhs;
    goto_trace_step.type=SSA_step.type;
    goto_trace_step.step_nr=step_nr;
    goto_trace_step.format_string=SSA_step.format_string;
    goto_trace_step.io_id=SSA_step.io_id;
    goto_trace_step.formatted=SSA_step.formatted;
    
    if(SSA_step.lhs.is_not_nil())
      goto_trace_step.value=prop_conv.get(SSA_step.lhs);
    
    for(std::list<exprt>::const_iterator
        j=SSA_step.converted_io_args.begin();
        j!=SSA_step.converted_io_args.end();
        j++)
    {
      const exprt &arg=*j;
      if(arg.is_constant() ||
         arg.id()==ID_string_constant)
        goto_trace_step.io_args.push_back(arg);
      else
      {
        exprt tmp=prop_conv.get(arg);
        goto_trace_step.io_args.push_back(tmp);
      }
    }

    if(SSA_step.is_assert() ||
       SSA_step.is_assume())
    {
      goto_trace_step.cond_expr=SSA_step.cond_expr;

      goto_trace_step.cond_value=
        prop_conv.prop.l_get(SSA_step.cond_literal).is_true();
    }

    if(SSA_step.is_assert())
    {
      // we stop after a violated assertion
      if(!goto_trace_step.cond_value)
        break;
    }
    else if(SSA_step.is_assume())
    {
      // assumptions can't be false
      // This is not necessarily true for partitioned_target_equation
      //assert(goto_trace_step.cond_value);
    }
  }
}

void prop_assertion_sumt::error_trace(const prop_convt &prop_conv, const namespacet &ns)
{
  status("Building error trace");

  goto_tracet goto_trace;

# ifndef USE_EXEC_ORDER_ERROR_TRACE
  // Original trace builder:
  build_goto_trace(equation, prop_conv, goto_trace);
# else
  // New exec order trace builder;
  build_exec_order_goto_trace(equation, prop_conv, goto_trace);
# endif

  #if 0
  if(options.get_option("vcd")!="")
  {
    if(options.get_option("vcd")=="-")
      output_vcd(ns, goto_trace, std::cout);
    else
    {
      std::ofstream out(options.get_option("vcd").c_str());
      output_vcd(ns, goto_trace, out);
    }
  }
  #endif

  switch(message_handler.get_ui())
  {
  case ui_message_handlert::PLAIN:
    std::cout << std::endl << "Counterexample:" << std::endl;
    show_goto_trace(std::cout, ns, goto_trace);
    break;

  case ui_message_handlert::OLD_GUI:
    show_goto_trace_gui(std::cout, ns, goto_trace);
    break;

  case ui_message_handlert::XML_UI:
    {
      xmlt xml;
      convert(ns, goto_trace, xml);
      std::cout << xml << std::endl;
    }
    break;

  default:
    assert(false);
  }
}
