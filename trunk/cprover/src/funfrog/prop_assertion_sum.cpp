/*******************************************************************

 Module: Propositional encoding of an SSA-form,
         And checking of its satisfiability

 Author: Ondrej Sery

\*******************************************************************/

#include <goto-symex/build_goto_trace.h>
#include <goto-symex/xml_goto_trace.h>
#include <time_stopping.h>
#include "prop_assertion_sum.h"

fine_timet global_satsolver_time;
fine_timet global_sat_conversion_time;

//#define TRACE_DEBUG //Use it to debug the trace of an error build

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

// Copied from build_goto_tarce.cpp
void prop_assertion_sumt::build_exec_order_goto_trace (
  partitioning_target_equationt &target,
  smtcheck_opensmt2t &decider,
  const namespacet &ns,
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

    if(!decider.is_assignemt_true(SSA_step.guard_literal))
      continue;

    if(SSA_step.is_assignment() &&
       SSA_step.assignment_type==symex_target_equationt::HIDDEN)
      continue;

    step_nr++;
    
    goto_trace.steps.push_back(goto_trace_stept());    
    goto_trace_stept &goto_trace_step=goto_trace.steps.back();
    
    goto_trace_step.thread_nr=SSA_step.source.thread_nr;
    goto_trace_step.pc=SSA_step.source.pc;
    goto_trace_step.comment=SSA_step.comment;
    goto_trace_step.lhs_object=SSA_step.original_lhs_object;
    goto_trace_step.type=SSA_step.type;
    goto_trace_step.step_nr=step_nr;
    goto_trace_step.format_string=SSA_step.format_string;
    goto_trace_step.io_id=SSA_step.io_id;
    goto_trace_step.formatted=SSA_step.formatted;
    goto_trace_step.identifier=SSA_step.identifier;

    if(SSA_step.ssa_lhs.is_not_nil())
      goto_trace_step.lhs_object_value=decider.get_value(SSA_step.ssa_lhs);
    
    if(SSA_step.ssa_full_lhs.is_not_nil())
    {
      goto_trace_step.full_lhs_value=decider.get_value(SSA_step.ssa_full_lhs);
    //  simplify(goto_trace_step.full_lhs_value, ns);
    }

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
        exprt tmp=decider.get_value(arg);
        goto_trace_step.io_args.push_back(tmp);
      }
    }

    // Stop condition + adding data to assume and assert steps
    if(SSA_step.is_assert() || SSA_step.is_assume())
    {
      goto_trace_step.cond_expr=SSA_step.cond_expr;
      goto_trace_step.cond_value=
    		  decider.is_assignemt_true(SSA_step.cond_literal);

      // we stop after a violated assertion
      if(SSA_step.is_assert() && !goto_trace_step.cond_value)
    	  break;
    }
  }
}

void prop_assertion_sumt::error_trace(smtcheck_opensmt2t &decider, const namespacet &ns)
{
	/* Basic print of the error trace as all variables values */
#ifdef TRACE_DEBUG
	MainSolver *mainSolver = decider.getMainSolver();
#endif
	Logic *logic = decider.getLogic();
	std::set<PTRef>* vars = decider.getVars();
	bool isOverAppox = false;
	std::string overapprox_str ("funfrog::c::unsupported_op2var");
	for(std::set<PTRef>::iterator iter = vars->begin(); iter != vars->end(); iter++)
	{
	// Print the var and its value
	char* name = logic->printTerm(*iter);
	std::string curr (name);
	if (curr.find(overapprox_str) != std::string::npos)
		isOverAppox = true;
#ifdef TRACE_DEBUG
	else
	{
		cout << " \\ " << name ;
		ValPair v1 = mainSolver->getValue(*iter);
		if (logic->isIteVar((*iter)))
			cout << ": (" << logic->printTerm(logic->getTopLevelIte(*iter)) << ")" << " = " << ((v1.val != 0) ? "true" : "false") << "\n";
		else
			cout << " = " << v1.val << "\n";
	}
#endif
		free(name);
	}

	// Clear all vars list before quit
	vars->clear(); delete vars;

	// Incase we use over approx to verify this example - gives a warning to the user!
	if (isOverAppox) {
		cout << "\nWARNING: Use over approximation. Cannot create an error trace. \n";
		return; // Cannot really print a trace
	}

	// Only if can build an error trace - give notice to the user
	status("Building error trace");

	goto_tracet goto_trace;
	build_exec_order_goto_trace(equation, decider, ns, goto_trace);

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
