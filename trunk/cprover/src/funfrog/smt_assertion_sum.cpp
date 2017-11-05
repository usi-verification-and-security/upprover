/*******************************************************************

 Module: Propositional encoding of an SSA-form,
         And checking of its satisfiability

 Author: Ondrej Sery

\*******************************************************************/

#include <time_stopping.h>
#include "smt_assertion_sum.h"
#include "error_trace.h"
#include "smt_partitioning_target_equation.h"
#include "solvers/smtcheck_opensmt2.h"



time_periodt global_satsolver_time;

/*******************************************************************

 Function: smt_assertion_sumt::assertion_holds

 Inputs:

 Outputs:

 Purpose: Checks if the given assertion of the GP holds

\*******************************************************************/
bool smt_assertion_sumt::assertion_holds(const assertion_infot &assertion, const namespacet &ns, smtcheck_opensmt2t& decider, interpolating_solvert& interpolator)
{
  bool sat=false;

  absolute_timet before, after;
  before=current_time();
  equation.convert(decider, interpolator);

  after=current_time();

  status() << "CONVERSION TIME: " << (after-before) << eom;

  // Decides the equation
  sat = is_satisfiable(decider);

  if (!sat)
  {
    return true;
  }
  else
  {
    return false;
  }
}

/*******************************************************************

 Function: smt_assertion_sumt::is_satisfiable

 Inputs:

 Outputs:

 Purpose: Checks if prepared formula is SAT

\*******************************************************************/

bool smt_assertion_sumt::is_satisfiable(
		smtcheck_opensmt2t& decider)
{
  absolute_timet before, after;
  before=current_time();
  bool r = decider.solve();
  after=current_time();
  solving_time = (after-before);
  global_satsolver_time += (after-before);
  status() << "SOLVER TIME: " << (after-before) << eom;
  status() << "RESULT: ";

  // solve it
  if (!r)
  {
      status() << "UNSAT - it holds!" << eom;
      return false;
    } else {
      status() << "SAT - doesn't hold" << eom;
      return true;
    }
}

void smt_assertion_sumt::error_trace(smtcheck_opensmt2t &decider, const namespacet &ns,
		std::map<irep_idt, std::string>& guard_expln)
{      
    // Only if can build an error trace - give notice to the user
    status() << ("Building error trace") << eom;
    
    error_tracet error_trace;
    
    error_tracet::isOverAppoxt isOverAppox = error_trace.is_trace_overapprox(decider);
    if (isOverAppox == error_tracet::isOverAppoxt::SPURIOUS)
    {
        // Same as in funfrog/error_tracet::show_goto_trace
        warning () << "\nWARNING: Use over approximation. Cannot create an error trace. \n";
        warning () << "         Use --logic with Different Logic to Try Creating an Error Trace." << eom;
        return; // Cannot really print a trace
    }

    error_trace.build_goto_trace(equation, decider);

    status () << "\nCounterexample:\n";
    error_trace.show_goto_trace(decider, std::cout, ns, guard_expln);
    status () << eom;
}
