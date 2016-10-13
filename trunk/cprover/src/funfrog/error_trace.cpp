#include "error_trace.h"

//#define TRACE_DEBUG //Use it to debug the trace of an error build


/*******************************************************************\

Function: error_trace::build_exec_order_goto_trace

  Inputs: SSA translation of the code and solver

 Outputs: a concrete trace (error trace with value)

 Purpose: To create a concrete error trace with concrete values

 Note: Copied from build_goto_tarce.cpp

\*******************************************************************/
void error_tracet::build_goto_trace (
  partitioning_target_equationt &target,
  smtcheck_opensmt2t &decider)
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

    std::string str(SSA_step.ssa_lhs.get("identifier").c_str());
    if (str.find("goto_symex::\\guard#") == 0){
      goto_trace_step.lhs_object=SSA_step.ssa_lhs;
    } else {
      goto_trace_step.lhs_object=SSA_step.original_lhs_object;
    }

    if (str.find("?retval") < str.size() ||
	str.find("$tmp::return_value")	< str.size())
    {
      goto_trace_step.format_string = "function return value";
    } else {
      goto_trace_step.format_string=SSA_step.format_string;
    }

    goto_trace_step.thread_nr=SSA_step.source.thread_nr;
    goto_trace_step.pc=SSA_step.source.pc;
    goto_trace_step.comment=SSA_step.comment;
    goto_trace_step.type=SSA_step.type;
    goto_trace_step.step_nr=step_nr;
    goto_trace_step.io_id=SSA_step.io_id;
    goto_trace_step.formatted=SSA_step.formatted;
    goto_trace_step.identifier=SSA_step.identifier;

    if(is_index_member_symbol(SSA_step.ssa_full_lhs)){
      goto_trace_step.full_lhs_value=decider.get_value(SSA_step.ssa_full_lhs);
    }
    else {
      goto_trace_step.full_lhs_value=decider.get_value(SSA_step.ssa_lhs);
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

/*******************************************************************\

Function: error_trace::show_trace_vars_value

  Inputs: solver with context so far

 Outputs: true if the current trace is affected by over-approximation
 	 	 done while solving the path constraints

 Purpose: To check that it is really a full concrete path

\*******************************************************************/
bool error_tracet::is_trace_overapprox(smtcheck_opensmt2t &decider)
{
	/* Basic print of the error trace as all variables values */
#ifdef TRACE_DEBUG
	MainSolver *mainSolver = decider.getMainSolver();
#endif
	Logic *logic = decider.getLogic();
	std::set<PTRef>* vars = decider.getVars();
	std::string overapprox_str ("funfrog::c::unsupported_op2var");
	std::string skip_debug_print ("funfrog::?call"); // Skip the print of this value due to assertion
	// violation in opensmt2 - worth debuging one day: Cnfizer.C:891: lbool Cnfizer::getTermValue(PTRef) const: Assertion `val != (lbool((uint8_t)2))' failed.
	for(std::set<PTRef>::iterator iter = vars->begin(); iter != vars->end(); iter++)
	{
	// Print the var and its value
	char* name = logic->printTerm(*iter);
	std::string curr (name);
	if (curr.find(overapprox_str) != std::string::npos)
		isOverAppox = true;
#ifdef TRACE_DEBUG
	else if (curr.find(skip_debug_print) != std::string::npos)
	{
		// Skip print
	}
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

	// True if there is some effect of over-approx of ops
	return isOverAppox;
}

/*******************************************************************\

Function: show_goto_trace

  Inputs:

 Outputs:

 Purpose:

 Note: Copied from goto_trace.cpp

\*******************************************************************/
void error_tracet::show_goto_trace(
  smtcheck_opensmt2t &decider,
  std::ostream &out,
  const namespacet &ns,
  std::map<irep_idt, std::string> &guard_expln)
{
    // In case we use over approximate to verify this example - gives a warning to the user!
	if (is_trace_overapprox(decider)) {
		cout << "\nWARNING: Use over approximation. Cannot create an error trace. \n";
		cout << "         Use --logic with Different Logic to Try Creating an Error Trace. \n";
		return; // Cannot really print a trace
	}


	unsigned prev_step_nr=0;
	bool first_step=true;

	for(goto_tracet::stepst::const_iterator
      it=goto_trace.steps.begin();
      it!=goto_trace.steps.end();
      it++)
	{
		switch(it->type)
		{
			// Don't print artificial instructions added for verification
			case goto_trace_stept::ASSUME:
			case goto_trace_stept::LOCATION:
			case goto_trace_stept::FUNCTION_CALL:
			case goto_trace_stept::FUNCTION_RETURN:
			case goto_trace_stept::SPAWN:
			case goto_trace_stept::ATOMIC_BEGIN:
			case goto_trace_stept::ATOMIC_END:
			case goto_trace_stept::DECL:
				break;

			case goto_trace_stept::ASSERT:
				if(!it->cond_value)
				{
					out << std::endl;
					out << "Violated property:" << std::endl;
					if(!it->pc->location.is_nil())
						out << "  " << it->pc->location << std::endl;
					out << "  " << it->comment << std::endl;

					if(it->pc->is_assert())
						out << "  " << from_expr(ns, "", it->pc->guard) << std::endl;

					out << std::endl;
				}
				break;

			case goto_trace_stept::ASSIGNMENT:
				if(it->pc->is_assign() ||
						it->pc->is_return() || // returns have a lhs!
						it->pc->is_function_call() ||
						(it->pc->is_other() && it->lhs_object.is_not_nil()))
				{
					if(prev_step_nr!=it->step_nr || first_step)
					{
						first_step=false;
						prev_step_nr=it->step_nr;
						show_state_header(out, it->thread_nr, it->pc->location, it->step_nr);
					}

					std::string str = guard_expln[it->lhs_object.get("identifier")];
					if (str != "")
						show_guard_value(out, str, it->full_lhs_value);
					else if (it->format_string != "")
						show_misc_value(out, it->format_string, it->full_lhs_value);
					else
						show_var_value(out, ns, it->lhs_object, it->lhs_object, it->full_lhs_value);
				}
				break;

			case goto_trace_stept::OUTPUT:
				if(it->formatted)
				{
					printf_formattert printf_formatter(ns);
					printf_formatter(id2string(it->format_string), it->io_args);
					printf_formatter.print(out);
					out << std::endl;
				}
				else
				{
					show_state_header(out, it->thread_nr, it->pc->location, it->step_nr);
					out << "  OUTPUT " << it->io_id << ":";

					for(std::list<exprt>::const_iterator
							l_it=it->io_args.begin();
							l_it!=it->io_args.end();
							l_it++)
					{
						if(l_it!=it->io_args.begin()) out << ";";
							out << " " << from_expr(ns, "", *l_it);
					}

					out << std::endl;
				}
				break;

			case goto_trace_stept::INPUT:
				show_state_header(out, it->thread_nr, it->pc->location, it->step_nr);
				out << "  INPUT " << it->io_id << ":";

				for(std::list<exprt>::const_iterator
						l_it=it->io_args.begin();
						l_it!=it->io_args.end();
						l_it++)
				{
					if(l_it!=it->io_args.begin()) out << ";";
						out << " " << from_expr(ns, "", *l_it);
				}

				out << std::endl;
				break;

			default:
				assert(false);
		}
	}
}

/*******************************************************************\

Function: show_state_header

  Inputs:

  Outputs:

  Purpose:

  Note: Copied from goto_trace.cpp

\*******************************************************************/
void error_tracet::show_state_header(
  std::ostream &out,
  const unsigned thread_nr,
  const locationt &location,
  unsigned step_nr)
{
  out << std::endl;

  if(step_nr==0)
    out << "Initial State";
  else
    out << "State " << step_nr;

  out << " " << location << " thread " << thread_nr << std::endl;
  out << "----------------------------------------------------" << std::endl;
}

void error_tracet::show_guard_value(
  std::ostream &out,
  const std::string &str,
  const exprt &value)
{
	out << "  [" << str <<  "] = " << value.get(ID_value) << std::endl;
}

void error_tracet::show_misc_value(
  std::ostream &out,
  const irep_idt &str,
  const exprt &value)
{
	out << "  \"" << str <<  "\" = " << value.get(ID_value) << std::endl;
}

/*******************************************************************\

Function: error_tracet::show_var_value

  Inputs:

  Outputs:

  Purpose:

\*******************************************************************/
void error_tracet::show_var_value(
  std::ostream &out,
  const namespacet &ns,
  const symbol_exprt &lhs_object,
  const exprt &full_lhs,
  const exprt &value)
{
	const irep_idt &identifier=lhs_object.get_identifier();
	out << "  ";
	show_expr(out, ns, identifier, full_lhs, false);
	out << " = ";
	show_expr(out, ns, identifier, value, value.is_nil());
	out << std::endl;
}

/*******************************************************************\

Function: error_tracet::show_expr

  Inputs:

  Outputs:

  Purpose:

\*******************************************************************/
void error_tracet::show_expr(
  std::ostream &out,
  const namespacet &ns,
  const irep_idt &identifier,
  const exprt &expr,
  bool is_removed)
{
	if (is_removed) // only for the value check
		out << "(assignment removed)";
	else if (expr.id() == ID_nil)
		out << "nil";
	else if (expr.id() == ID_constant)
		out << expr.get(ID_value);
	else
		out << from_expr(ns, identifier, expr);
}

/*******************************************************************\

Function: error_tracet::is_index_member_symbol

  Inputs:

  Outputs:

  Purpose:

  Note: Copied from goto_trace.cpp

\*******************************************************************/
bool error_tracet::is_index_member_symbol(const exprt &src)
{
	  if(src.id()==ID_index)
	    return is_index_member_symbol(src.op0());
	  else if(src.id()==ID_member)
	    return is_index_member_symbol(src.op0());
	  else if(src.id()==ID_symbol)
	    return true;
	  else
	    return false;
}
