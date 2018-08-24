/* 
 * File:   smt_assertion_no_partition.cpp
 * Author: karinek
 * 
 * Created on 27 April 2017, 10:56
 */

#include <goto-symex/build_goto_trace.h>
#include <goto-programs/xml_goto_trace.h>
#include <util/find_symbols.h>
#include <ansi-c/expr2c.h>
#include <util/ui_message.h>
#include "../error_trace.h"

#include "smt_assertion_no_partition.h"
#include "../solvers/smtcheck_opensmt2.h"


extern timet global_satsolver_time;

/*******************************************************************

 Function: smt_assertion_no_partitiont::assertion_holds

 Inputs:

 Outputs:

 Purpose: Checks if the given assertion of the GP holds

\*******************************************************************/
bool smt_assertion_no_partitiont::assertion_holds(smtcheck_opensmt2t& decider)
{
  bool sat=false;

  auto before=timestamp();
  equation.convert(decider);

  auto after=timestamp();

  status() << "CONVERSION TIME: " << time_gap(after,before) << eom;

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

 Function: smt_assertion_no_partitiont::is_satisfiable

 Inputs:

 Outputs:

 Purpose: Checks if prepared formula is SAT

\*******************************************************************/

bool smt_assertion_no_partitiont::is_satisfiable(
		smtcheck_opensmt2t& decider)
{
  auto before=timestamp();
  bool r = decider.solve();
  auto after=timestamp();
  //solving_time = time_gap(after,before);
  //global_satsolver_time += solving_time; // TODO
  status() << "SOLVER TIME: " << time_gap(after,before) << eom;
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

void smt_assertion_no_partitiont::error_trace(smtcheck_opensmt2t &decider, const namespacet &ns,
		std::map<irep_idt, std::string>& guard_expln)
{      
    // Only if can build an error trace - give notice to the user
    status() << ("Building error trace") << eom;
    
    error_tracet error_trace;
    
    error_tracet::isOverAppoxt isOverAppox = error_trace.is_trace_overapprox(decider, get_steps_exec_order());
    if (isOverAppox == error_tracet::isOverAppoxt::SPURIOUS)
    {
        // Same as in funfrog/error_tracet::show_goto_trace
        status()  << "\nWARNING: Use over approximation. Cannot create an error trace." << eom;
        status()  << "         Use --logic with Different Logic to Try Creating an Error Trace." << eom;
        return; // Cannot really print a trace
    }

    error_trace.build_goto_trace(get_steps_exec_order(), decider);

    result() << "\nCounterexample:" << eom;
    error_trace.show_goto_trace(result (), ns, guard_expln);
    result () << eom;
}

