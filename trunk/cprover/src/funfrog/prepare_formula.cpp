/*******************************************************************

 Module: Convert an SSA-form to smt, and checking of its satisfiability

\*******************************************************************/

#include <util/time_stopping.h>
#include "prepare_formula.h"
#include "error_trace.h"
#include "solvers/smtcheck_opensmt2.h"
#include "partitioning_target_equation.h"
#include "interface/solver/solver.h"

time_periodt global_satsolver_time;

/*******************************************************************

 Function: smt_formulat::convert_to_formula

 Inputs:

 Outputs:

 Purpose: Converts SSA form to SMT formula

\*******************************************************************/
void prepare_formulat::convert_to_formula(check_opensmt2t &decider, interpolating_solvert &interpolator)
{
  absolute_timet before, after;
  before=current_time();
  equation.convert(decider, interpolator);

  after=current_time();

    message.status() << "CONVERSION TIME: " << (after-before) << message.eom;
}

/*******************************************************************

 Function: smt_assertion_sumt::is_satisfiable

 Inputs:

 Outputs:

 Purpose: Checks if prepared formula is SAT

\*******************************************************************/

bool prepare_formulat::is_satisfiable(
		solvert& decider)
{
  absolute_timet before, after;
  before=current_time();
  bool is_sat = decider.solve();
  after=current_time();
    message.status() << "SOLVER TIME: " << (after-before) << message.eom;
    message.status() << "RESULT: ";

  // solve it
  if (is_sat)
  {
      message.status() << "SAT - doesn't hold" << message.eom;
    return true;
  }
  else
  {
      message.status() << "UNSAT - it holds!" << message.eom;
    return false;
  }
  //  return is_sat;
}
/*******************************************************************

 Function:
 Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
void prepare_formulat::error_trace(check_opensmt2t &decider, const namespacet &ns,
		std::map<irep_idt, std::string>& guard_expln)
{      
    // Only if can build an error trace - give notice to the user
    message.status() << ("Building error trace") << message.eom;
    
    error_tracet error_trace;
    
    error_tracet::isOverAppoxt isOverAppox = error_trace.is_trace_overapprox(decider, equation.get_steps_exec_order());
    if (isOverAppox == error_tracet::isOverAppoxt::SPURIOUS)
    {
        // Same as in funfrog/error_tracet::show_goto_trace
        message.warning () << "\nWARNING: Use over approximation. Cannot create an error trace. \n";
        message.warning () << "         Use --logic with Different Logic to Try Creating an Error Trace." << message.eom;
        return; // Cannot really print a trace
    }

    error_trace.build_goto_trace(equation.get_steps_exec_order(), decider);

    message.result () << "\nCounterexample:\n";
    error_trace.show_goto_trace(message.result(), ns, guard_expln);
    message.result () << message.eom;
}
