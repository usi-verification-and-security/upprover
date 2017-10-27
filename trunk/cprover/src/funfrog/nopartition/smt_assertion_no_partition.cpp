/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

/* 
 * File:   smt_assertion_no_partition.cpp
 * Author: karinek
 * 
 * Created on 27 April 2017, 10:56
 */

#include <goto-symex/build_goto_trace.h>
#include <goto-programs/xml_goto_trace.h>
#include <find_symbols.h>
#include <ansi-c/expr2c.h>
#include <time_stopping.h>
#include <ui_message.h>
#include "../error_trace.h"

#include "smt_assertion_no_partition.h"
#include "../solvers/smtcheck_opensmt2.h"


extern time_periodt global_satsolver_time;

/*******************************************************************

 Function: smt_assertion_no_partitiont::assertion_holds

 Inputs:

 Outputs:

 Purpose: Checks if the given assertion of the GP holds

\*******************************************************************/
bool smt_assertion_no_partitiont::assertion_holds(smtcheck_opensmt2t& decider)
{
  bool sat=false;

  absolute_timet before, after;
  before=current_time();
  equation.convert(decider);

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

 Function: smt_assertion_no_partitiont::is_satisfiable

 Inputs:

 Outputs:

 Purpose: Checks if prepared formula is SAT

\*******************************************************************/

bool smt_assertion_no_partitiont::is_satisfiable(
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

void smt_assertion_no_partitiont::error_trace(smtcheck_opensmt2t &decider, const namespacet &ns,
		std::map<irep_idt, std::string>& guard_expln)
{      
    // Only if can build an error trace - give notice to the user
    status() << ("Building error trace") << eom;
    
    error_tracet error_trace;
    
    error_tracet::isOverAppoxt isOverAppox = error_trace.is_trace_overapprox(decider);
    if (isOverAppox == error_tracet::isOverAppoxt::SPURIOUS)
    {
        // Same as in funfrog/error_tracet::show_goto_trace
        cout << "\nWARNING: Use over approximation. Cannot create an error trace. \n";
        cout << "         Use --logic with Different Logic to Try Creating an Error Trace. \n";
        return; // Cannot really print a trace
    }

    error_trace.build_goto_trace(equation, decider);

    std::cout << std::endl << "Counterexample:" << std::endl;
    
    error_trace.show_goto_trace(decider, std::cout, ns, guard_expln);
}

