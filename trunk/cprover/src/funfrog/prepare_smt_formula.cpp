/*******************************************************************

 Module: Convert an SSA-form to smt,
         And checking of its satisfiability

 Author:

\*******************************************************************/

#include "prepare_smt_formula.h"
#include "error_trace.h"
#include "smt_partitioning_target_equation.h"
#include "solvers/smtcheck_opensmt2.h"
#include <funfrog/utils/time_utils.h>

timet global_satsolver_time;

/*******************************************************************

 Function: smt_formulat::convert_to_formula

 Inputs:

 Outputs:

 Purpose: Converts SSA form to SMT formula

\*******************************************************************/
void prepare_smt_formulat::convert_to_formula(smtcheck_opensmt2t &decider, interpolating_solvert &interpolator)
{
  auto before=timestamp();
  equation.convert(decider, interpolator);

  auto after=timestamp();

  status() << "CONVERSION TIME: " << time_gap(after,before) << eom;
}

/*******************************************************************

 Function: smt_assertion_sumt::is_satisfiable

 Inputs:

 Outputs:

 Purpose: Checks if prepared formula is SAT

\*******************************************************************/

bool prepare_smt_formulat::is_satisfiable(
		smtcheck_opensmt2t& decider)
{
  auto before=timestamp();
  bool is_sat = decider.solve();
  auto after=timestamp();
  status() << "SOLVER TIME: " << time_gap(after,before) << eom;
  status() << "RESULT: ";

  // solve it
  if (is_sat)
  {
    status() << "SAT - doesn't hold" << eom;
    return true;
  }
  else
  {
    status() << "UNSAT - it holds!" << eom;
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
void prepare_smt_formulat::error_trace(smtcheck_opensmt2t &decider, const namespacet &ns,
		std::map<irep_idt, std::string>& guard_expln)
{      
    // Only if can build an error trace - give notice to the user
    status() << ("Building error trace") << eom;
    
    error_tracet error_trace;
    
    error_tracet::isOverAppoxt isOverAppox = error_trace.is_trace_overapprox(decider, equation.get_steps_exec_order());
    if (isOverAppox == error_tracet::isOverAppoxt::SPURIOUS)
    {
        // Same as in funfrog/error_tracet::show_goto_trace
        warning () << "\nWARNING: Use over approximation. Cannot create an error trace. \n";
        warning () << "         Use --logic with Different Logic to Try Creating an Error Trace." << eom;
        return; // Cannot really print a trace
    }

    error_trace.build_goto_trace(equation.get_steps_exec_order(), decider);

    result () << "\nCounterexample:\n";
    error_trace.show_goto_trace(result (), ns, guard_expln);
    result () << eom;
}
