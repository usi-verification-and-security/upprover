/*******************************************************************

 Module: Error Trace printing for SMT encoding in HiFrog

 Author:

\*******************************************************************/

#include "error_trace.h"

#include "solvers/smtcheck_opensmt2_cuf.h"
#include <funfrog/utils/naming_helpers.h>
#include <langapi/language_util.h>
#include <goto-programs/printf_formatter.h>

//#define DEBUG_TRACE //Use it to debug the trace of an error build
#ifdef DEBUG_TRACE
#include <iostream>
#endif

/*******************************************************************\
Function: error_trace::build_exec_order_goto_trace
 Inputs: SSA translation of the code and solver
 Outputs: a concrete trace (error trace with value)
 Purpose: To create a concrete error trace with concrete values
 Note: customized build_goto_trace() in build_goto_trace.cpp
 * ANY PROBLEMS with values, you should start look for here!
\*******************************************************************/
void error_tracet::build_goto_trace(
        const SSA_steps_orderingt &SSA_steps,
        ssa_solvert &decider)
{
  auto convertor = decider.get_convertor();
  solvert* solver = decider.get_solver();
  unsigned step_nr=0;

  for(auto ssa_step_ptr : SSA_steps)
  {
    const auto & SSA_step = *ssa_step_ptr;
    if (!solver->is_assignment_true(convertor->convert_bool_expr(SSA_step.guard_handle)))
      continue;

    if(SSA_step.is_assignment() &&
       SSA_step.assignment_type==symex_target_equationt::assignment_typet::HIDDEN)
      continue;

    std::string str(SSA_step.ssa_lhs.get(ID_identifier).c_str());
    if (is_cprover_rounding_mode_var(str))
    	continue;

    if (is_cprover_builtins_var(str))
    	continue;

    if (str.find(CProverStringConstants::DYNAMIC_OBJ)!=std::string::npos)
        continue;
        
    // Don't print artificial instructions added for verification
    if(SSA_step.ssa_lhs.id()==ID_symbol &&
       str.find(HifrogStringConstants::FUN_RETURN)!=std::string::npos)
        continue;

    //skip unsuported vars from error trace
    if (is_unsupported_var_name(str))
        continue;

    //skip array vars from error trace
    if (SSA_step.ssa_lhs.get(ID_type)==ID_array)
        continue;

    step_nr++;

    goto_trace.steps.push_back(goto_trace_stept());
    goto_trace_stept &goto_trace_step = goto_trace.steps.back();

    goto_trace_step.thread_nr = SSA_step.source.thread_nr;
    goto_trace_step.pc = SSA_step.source.pc;
    goto_trace_step.comment = SSA_step.comment;
    goto_trace_step.type = SSA_step.type;
    goto_trace_step.hidden = SSA_step.hidden;
    goto_trace_step.step_nr = step_nr;
    goto_trace_step.format_string = SSA_step.format_string;
    goto_trace_step.io_id = SSA_step.io_id;
    goto_trace_step.formatted = SSA_step.formatted;
    goto_trace_step.called_function = SSA_step.called_function;

    if(SSA_step.original_full_lhs.is_not_nil())
    {
        goto_trace_step.full_lhs = SSA_step.original_full_lhs;
    }

    if(SSA_step.ssa_full_lhs.is_not_nil())
    {
        goto_trace_step.full_lhs_value = solver->get_value(SSA_step.ssa_full_lhs);
    }

    /* Print nice return value info */
    if (str.find(HifrogStringConstants::FUN_RETURN) < str.size() ||
        str.find(HifrogStringConstants::TMP_RETURN) < str.size())
    {
        goto_trace_step.format_string = "function return value";
    } else {
        goto_trace_step.format_string=SSA_step.format_string;
    }

    for(const auto & arg : SSA_step.converted_io_args)
    {
      if(arg.is_constant() ||
         arg.id()==ID_string_constant)
        goto_trace_step.io_args.push_back(arg);
      else
      {
        exprt tmp=solver->get_value(arg);
        goto_trace_step.io_args.push_back(tmp);
      }
    }

    // Stop condition + adding data to assume and assert steps
    // note cporover 5.12 has added is_goto() as well
    if(SSA_step.is_assert() || SSA_step.is_assume() || SSA_step.is_goto())
    {
      goto_trace_step.cond_expr=SSA_step.cond_expr;
      goto_trace_step.cond_value = solver->is_assignment_true(
          convertor->convert_bool_expr(SSA_step.cond_handle));
      
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
error_tracet::isOverAppoxt error_tracet::is_trace_overapprox(ssa_solvert &decider, const SSA_steps_orderingt &SSA_steps)
{
    solvert* solver = decider.get_solver();
    convertort* convertor = decider.get_convertor();
    if (solver->is_overapprox_encoding())
    {
        // Check the error trace symbols,
        for(SSA_steps_orderingt::const_iterator
            it=SSA_steps.begin();
            it!=SSA_steps.end();
            it++)
        {
            const SSA_stept &SSA_step = **it;
            
            if (!solver->is_assignment_true(convertor->convert_bool_expr(SSA_step.guard_handle)))
                continue;
            if(SSA_step.is_assignment() && SSA_step.assignment_type==symex_target_equationt::assignment_typet::HIDDEN)
                continue;
       
            std::string str(SSA_step.ssa_lhs.get("identifier").c_str());
            if (is_unsupported_var_name(str)) {
                isOverAppox = error_tracet::isOverAppoxt::SPURIOUS;
                break;
            }
        }
    }
    
    if (isOverAppox != error_tracet::isOverAppoxt::SPURIOUS)
    	isOverAppox = error_tracet::isOverAppoxt::REAL;

    // True if there is some effect of over-approx of ops
    return isOverAppox;
}

/*******************************************************************\

Function: show_goto_trace

Note: Copied from goto_trace.cpp

\*******************************************************************/
void error_tracet::show_goto_trace(
    messaget::mstreamt &out,
    const namespacet &ns,
    std::map<irep_idt, std::string> &guard_expln)
{
    // In case we use over approximate to verify this example - gives a warning to the user!
    assert (isOverAppox != error_tracet::isOverAppoxt::UNKNOWN);

    if (isOverAppox == error_tracet::isOverAppoxt::SPURIOUS) {
        std::cout << "\nWARNING: Use over approximation. Cannot create an error trace. \n";
        std::cout << "         Use --logic with Different Logic to Try Creating an Error Trace. \n";
        return; // Cannot really print a trace
    }
    
    unsigned prev_step_nr=0;
    bool first_step=true;

    for(const auto step : goto_trace.steps)
    {
        switch(step.type)
        {
            // Don't print artificial instructions added for verification
            case goto_trace_stept::typet::ASSUME:
            case goto_trace_stept::typet::LOCATION:
            case goto_trace_stept::typet::FUNCTION_CALL:
            case goto_trace_stept::typet::FUNCTION_RETURN:
            case goto_trace_stept::typet::SPAWN:
            case goto_trace_stept::typet::ATOMIC_BEGIN:
            case goto_trace_stept::typet::ATOMIC_END:
            case goto_trace_stept::typet::DECL:
            case goto_trace_stept::typet::MEMORY_BARRIER:
            case goto_trace_stept::typet::DEAD:
            case goto_trace_stept::typet::GOTO:
                    break;

            case goto_trace_stept::typet::CONSTRAINT:
              assert(false); // KE: show me this case!
              break;

            case goto_trace_stept::typet::SHARED_READ:
            case goto_trace_stept::typet::SHARED_WRITE:
              // Unsupported here, probably is unsupported var
              isOverAppox = error_tracet::isOverAppoxt::SPURIOUS;
              // FIXME: change against unsupported tables
              break;

            case goto_trace_stept::typet::ASSERT:
                if(!step.cond_value)
                {
                    // KE: keep the same format of prints as in goto-programs/goto_trace.cpp
                    out << "\n";
                    out << "Violated property:\n  " <<
                        step.pc->source_location <<
                        "\n  " << step.comment <<
                        "\n  " << from_expr(ns, "", step.pc->guard);

                    out << "\n";
                }
                break;

            case goto_trace_stept::typet::ASSIGNMENT:
                if(step.pc->is_assign() ||
                        step.pc->is_return() || // returns have a lhs!
                        step.pc->is_function_call() ||
                        (step.pc->is_other() && step.get_lhs_object()->is_not_nil()))
                {
                    if(prev_step_nr!=step.step_nr || first_step)
                    {
                        first_step=false;
                        prev_step_nr=step.step_nr;
                        show_state_header(out, step.thread_nr, step.pc->source_location, step.step_nr);
                    }

                    std::string str = guard_expln[step.get_lhs_object()->get_identifier()];
#ifdef DEBUG_TRACE
                    std::cout << "guar explain first: " << guard_expln.begin()->first.c_str() << " second: "<< guard_expln.begin()->second.c_str() << "\n";
#endif
                    if (str != "")
                        show_guard_value(out, str, step.full_lhs_value);
                    else if (step.format_string != "")
                        show_misc_value(out, step.format_string, step.full_lhs_value);
                    else
                        show_var_value(out, ns, step.get_lhs_object(), step.full_lhs, step.full_lhs_value);
                }
                break;

            case goto_trace_stept::typet::OUTPUT:
                if(step.formatted)
                {
                    printf_formattert printf_formatter(ns);
                    printf_formatter(id2string(step.format_string), step.io_args);
                    printf_formatter.print(out);
                    out << "\n";
                }
                else
                {
                    show_state_header(out, step.thread_nr, step.pc->source_location, step.step_nr);
                    out << "  OUTPUT " << step.io_id << ":";

                    for(std::list<exprt>::const_iterator
                                l_it=step.io_args.begin();
                                l_it!=step.io_args.end();
                                l_it++)
                    {
                        if(l_it!=step.io_args.begin()) out << ";";
                            out << " " << from_expr(ns, "", *l_it);
                    }

                        out << '\n';
                }
                break;

            case goto_trace_stept::typet::INPUT:
                show_state_header(out, step.thread_nr, step.pc->source_location, step.step_nr);
                out << "  INPUT " << step.io_id << ":";

                for(std::list<exprt>::const_iterator
                        l_it=step.io_args.begin();
                        l_it!=step.io_args.end();
                        l_it++)
                {
                    if(l_it!=step.io_args.begin()) out << ";";
                        out << " " << from_expr(ns, "", *l_it);
                }

                out << '\n';
                break;

            default:
#ifdef DEBUG_TRACE
                std::cout << "Error " << step.type << '\n';
#endif
                assert(false);
        }
    }
}

/*******************************************************************\

Function: show_state_header

 Note: Copied from goto_trace.cpp

\*******************************************************************/
void error_tracet::show_state_header(
  std::ostream &out,
  const unsigned thread_nr,
  const source_locationt &location,
  unsigned step_nr)
{
  out << '\n';

  if(step_nr==0)
    out << "Initial State";
  else
    out << "State " << step_nr;

  out << " " << location << '\n';
  out << "----------------------------------------------------" << '\n';
}

void error_tracet::show_guard_value(
  std::ostream &out,
  const std::string &str,
  const exprt &value)
{
	out << "  [" << str <<  "] = " << value.get(ID_value) << '\n';
}

void error_tracet::show_misc_value(
  std::ostream &out,
  const irep_idt &str,
  const exprt &value)
{
	out << "  \"" << str <<  "\" = " << value.get(ID_value) << '\n';
}

/*******************************************************************\

Function: error_tracet::show_var_value

 Purpose: print concrete values in error trace

\*******************************************************************/
void error_tracet::show_var_value(
  messaget::mstreamt &out,
  const namespacet &ns,
  const optionalt<symbol_exprt> &lhs_object,
  const exprt &full_lhs,
  const exprt &value)
{
//    irep_idt identifier;
//    if(lhs_object.has_value())
//        identifier = lhs_object->get_identifier();
    
    out << "  ";
    show_expr(out, ns, lhs_object, full_lhs, false);
    out << " = ";
    show_expr(out, ns, lhs_object, value, value.is_nil());
    out << "\n";
}

/*******************************************************************\

Function: error_tracet::show_expr

  Note: similar to static void trace_value()

\*******************************************************************/
void error_tracet::show_expr(
    messaget::mstreamt &out,
    const namespacet &ns,
    const optionalt<symbol_exprt> &lhs_object,
    const exprt &full_lhs,
    bool is_removed)
{
    irep_idt identifier;
    
    if (lhs_object.has_value())
        identifier = lhs_object->get_identifier();
    if (is_removed) // only for the value check
        out << "(assignment removed)";
    else if (full_lhs.id() == ID_constant)
      out << full_lhs.get(ID_value); //used in CEX of QF_UF eg: n0, n1
    else
        out << from_expr(ns, identifier, full_lhs);
}

//CPROVER 5.12
//    out << from_expr(ns, identifier, full_lhs) << '=';
//
//    if (value.is_nil())
//        out << "(assignment removed)";
//    else {
//        out << from_expr(ns, identifier, value);
//    }
//
//    out << '\n';

/*******************************************************************\

CUF-version of the CE-formula
used in the theory-refinement algorithm

Purpose: CEX extraction
\*******************************************************************/
void error_tracet::build_goto_trace_formula(
    std::vector<exprt> &exprs,
    std::map<const exprt, int> &model,
    solvert &solver)
{
  std::set<exprt> vars;
  std::map<const irep_idt, std::vector<exprt>*> non_interp_classes;
  int max_interp_value = 0;
  
  for (auto it = exprs.begin(); it != exprs.end(); ++it)
  {
    getVarsInExpr(*it, vars);
  }
  
  for (auto it = vars.begin(); it != vars.end(); ++it)
  {
    exprt val = solver.get_value(*it);
    
    const irep_idt val_val = val.get(ID_value);
    if (val_val.size() == 0) continue;
    
    int ptr;
    //handling CUF values (n, u, a) in the CE-formula construction
    if (val_val[0] == 'n'){
      ptr = atoi(val_val.c_str() + 1);
      // store the max value among n-values (will be used after the loop):
      if (ptr > max_interp_value) max_interp_value = ptr;
    } else if (val_val[0] == 'a'){
      //show the example if reaches here
      assert(0);
    } else if (val_val[0] == 'u'){
      if (non_interp_classes.find(val_val) == non_interp_classes.end()){
        non_interp_classes[val_val] = new std::vector<exprt>();
      }
      non_interp_classes[val_val]->push_back(*it);
      // the interpretations for u-values will be computed after this loop
      continue;
    } else if (val_val == "1"){
      ptr = 1;
    } else if (val_val == "0"){
      ptr = 0;
    } else {
      ptr = atoi(val.get(ID_value).c_str());
    }
    
    model[*it] = ptr;
  }
  
  // computing interpretations for u-values:
    for (auto & item: non_interp_classes){
    int l1 = ++max_interp_value;
    for (unsigned int i = 0; i < item.second->size(); i++)
    {
      model[item.second->at(i)] = l1;
    }
  }
}

/*******************************************************************\
 * experimental LRA-version of the CE-formula (obsolete).
 * Only used for debugging / comparison with CUF-version
 Currently this is not in the theory-refinement core algorithm
\*******************************************************************/
/*
void error_tracet::build_goto_trace_formula (
  partitioning_target_equationt &target,
  smtcheck_opensmt2t &decider,
  smtcheck_opensmt2t_lra &decider2)
{
  decider2.new_partition();

  std::map<const irep_idt, std::vector<literalt>*> non_interp_classes;
  int max_interp_value = 0;

  const SSA_steps_orderingt& SSA_steps = target.get_steps_exec_order();

  for(SSA_steps_orderingt::const_iterator
      it=SSA_steps.begin();
      it!=SSA_steps.end();
      it++)
  {
    const SSA_stept &SSA_step=**it;

    if(!decider.is_assignment_true(SSA_step.guard_literal))
      continue;

    if(SSA_step.is_assignment() &&
       SSA_step.assignment_type==symex_target_equationt::assignment_typet::HIDDEN)
      continue;

    std::string str(SSA_step.ssa_lhs.get("identifier").c_str());
    if (is_cprover_rounding_mode_var(str))
    	continue;

    if (is_cprover_builtins_var(str))
    	continue;

    if (str.find(CProverStringConstants::DYNAMIC_OBJ)!=std::string::npos)
        continue;

    if(SSA_step.ssa_lhs.id()==ID_symbol &&
       str.find(HifrogStringConstants::FUN_RETURN)!=std::string::npos)
        continue;


    if (is_unsupported_var_name(str))
        continue;

    if (SSA_step.ssa_lhs.get(ID_type)==ID_array)
        continue;

    if(SSA_step.ssa_full_lhs.is_not_nil())
    {
    	exprt val;
        if(is_index_member_symbol(SSA_step.ssa_full_lhs)){
            val=decider.get_value(SSA_step.ssa_full_lhs);
        }
        else {
            val=decider.get_value(SSA_step.ssa_lhs);
        }

        const irep_idt val_val = val.get(ID_value);
        if (val_val.size() == 0) continue;

        literalt ltr;
        if (val_val[0] == 'n'){
          int interp_value = atoi(val.get(ID_value).c_str() + 1);
          if (interp_value > max_interp_value) max_interp_value = interp_value;
          ltr = decider2.const_from_str(val.get(ID_value).c_str() + 1);
        } else if (val_val[0] == 'a'){
          ltr = decider2.const_from_str("777");
        } else if (val_val[0] == 'u'){
          if (non_interp_classes.find(val_val) == non_interp_classes.end()){
            non_interp_classes[val_val] = new std::vector<literalt>();
          }
          non_interp_classes[val_val]->push_back(decider2.convert_bool_expr(SSA_step.ssa_lhs));
          continue;
        } else if (val.get(ID_value) == "1"){
          ltr = decider2.get_const_literal(true);
        } else if (val.get(ID_value) == "0"){
          ltr = decider2.get_const_literal(false);
        } else {
          continue;
        }

	decider2.set_equal(ltr, decider2.convert_bool_expr(SSA_step.ssa_lhs));
    }
  }
  for (std::map<const irep_idt, std::vector<literalt>*>::iterator
      it=non_interp_classes.begin(); it!=non_interp_classes.end(); ++it){
    literalt l1 = decider2.const_from_str(std::to_string(++max_interp_value).c_str());
    for (unsigned int i = 0; i < it->second->size(); i++){
      decider2.set_equal(l1, it->second->at(i));
    }
  }
  decider2.close_partition();
  std::cout << "CE-formula constructed\n";
}
*/