/*******************************************************************

 Module: Propositional encoding of an SSA-form,
         And checking of its satisfiability

 Author: Ondrej Sery

\*******************************************************************/

#include <goto-symex/build_goto_trace.h>
#include <find_symbols.h>
#include <ansi-c/expr2c.h>
#include <time_stopping.h>
#include <loopfrog/memstat.h>

#include "prop_assertion_sum.h"

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
  stream_message_handlert message_handler(out);

  bool sat=false;

  decider.set_message_handler(message_handler);
  decider.set_verbosity(10);

  fine_timet before, after;
  before=current_time();
  equation.convert(decider, summarization_context, interpolator);
  after=current_time();
  global_sat_conversion_time += (after-before);

  if (out.good())
    out << "CONVERSION TIME: "<< time2string(after-before) << std::endl;

  // Decides the equation
  sat = is_satisfiable(decider);

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

 Function: prop_assertion_sumt::is_satisfiable

 Inputs:

 Outputs:

 Purpose: Checks if prepared formula is SAT

\*******************************************************************/

bool prop_assertion_sumt::is_satisfiable(
  decision_proceduret &decision_procedure)
{
  if (out.good())
    out <<std::endl<<"RESULT:"<<std::endl;

  fine_timet before, after;
  before=current_time();
  decision_proceduret::resultt r = decision_procedure.dec_solve();
  after=current_time();
  if (out.good())
    out << "SOLVER TIME: "<< time2string(after-before) << std::endl;

  solving_time = (after-before);
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
