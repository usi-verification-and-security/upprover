/*******************************************************************

 Module: Convert an SSA-form to smt, and checking of its satisfiability

\*******************************************************************/

#include "formula_manager.h"

#include "error_trace.h"
#include <funfrog/utils/time_utils.h>
#include "partitioning_target_equation.h"
#include "interface/ssa_solvert.h"

/*******************************************************************
 Purpose: Converts SSA form to SMT formula

\*******************************************************************/
void formula_managert::convert_to_formula(convertort &convertor, interpolating_solvert &interpolator)
{
    auto before=timestamp();
    equation.convert(convertor, interpolator);

    auto after=timestamp();

    message.status() << "CONVERSION TIME: " << time_gap(after,before) << message.eom;
}

/*******************************************************************
 Purpose: Checks if prepared formula is SAT

\*******************************************************************/

bool formula_managert::is_satisfiable(solvert& decider)
{
    auto before=timestamp();
    bool is_sat = decider.solve();
    auto after=timestamp();
    message.status() << "SOLVER TIME: " << time_gap(after,before) << message.eom;
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
 Purpose:

\*******************************************************************/
void formula_managert::error_trace(ssa_solvert &decider, const namespacet &ns,
                                   std::map<irep_idt, std::string> &guard_expln)
{      
    // Only if can build an error trace - give notice to the user
    message.status() << ("Building error trace") << message.eom;
    
    error_tracet error_trace;
    solvert* solver = decider.get_solver();
    
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
