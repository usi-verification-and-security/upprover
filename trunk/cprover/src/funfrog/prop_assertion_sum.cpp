/*******************************************************************

 Module: Propositional encoding of an SSA-form,
         And checking of its satisfiability

 Author: Ondrej Sery

\*******************************************************************/

#include <goto-symex/build_goto_trace.h>
#include <goto-symex/xml_goto_trace.h>
#include <time_stopping.h>
#include "prop_assertion_sum.h"
#include "error_trace.h"

fine_timet global_satsolver_time;
fine_timet global_sat_conversion_time;

/*******************************************************************

 Function: prop_assertion_sumt::assertion_holds

 Inputs:

 Outputs:

 Purpose: Checks if the given assertion of the GP holds

\*******************************************************************/

bool prop_assertion_sumt::assertion_holds(const assertion_infot &assertion, const namespacet &ns, smtcheck_opensmt2t& decider, interpolating_solvert& interpolator)
{
  //stream_message_handlert message_handler(out);

  bool sat=false;

  fine_timet before, after;
  before=current_time();
  equation.convert(decider, interpolator);


  after=current_time();
//  global_sat_conversion_time += (after-before);

  status() << "CONVERSION TIME: " << (after-before) << eom;

  // Decides the equation
  sat = is_satisfiable(decider);

  //unsigned long this_mem = current_memory();
  //if (this_mem > max_memory_used)
  //  max_memory_used = this_mem;

  if (!sat)
  {
    status("ASSERTION IS TRUE");
    return true;
  }
  else
  {
    status("ASSERTION IS VIOLATED");
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
		smtcheck_opensmt2t& decider)
{
  status("RESULT");
  fine_timet before, after;
  before=current_time();
  bool r = decider.solve();
  after=current_time();
  status() << "SOLVER TIME: " << (after-before) << eom;

  solving_time = (after-before);
  global_satsolver_time += (after-before);

  // solve it
  if (!r)
  {
      status("UNSAT - it holds!");
      return false;
    } else {
      status("SAT - doesn't hold");
      return true;
    }

}

void prop_assertion_sumt::error_trace(smtcheck_opensmt2t &decider, const namespacet &ns,
		std::map<irep_idt, std::string>& guard_expln)
{
	error_tracet error_trace;

	// Only if can build an error trace - give notice to the user
	status("Building error trace");

	error_trace.build_goto_trace(equation, decider);

	error_trace.show_goto_trace(decider, std::cout, ns, guard_expln);
}
