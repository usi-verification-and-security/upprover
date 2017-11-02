#include "error_trace.h"
#include "hifrog.h"
#include "solvers/smtcheck_opensmt2_cuf.h"
#include <ansi-c/printf_formatter.h>
#include "nopartition/smt_symex_target_equation.h"
#include "smt_partitioning_target_equation.h"
#include "solvers/smtcheck_opensmt2_lra.h"



//#define TRACE_DEBUG //Use it to debug the trace of an error build


/*******************************************************************\

Function: error_trace::build_exec_order_goto_trace

  Inputs: SSA translation of the code and solver

 Outputs: a concrete trace (error trace with value)

 Purpose: To create a concrete error trace with concrete values

 Note: Copied from build_goto_tarce.cpp
 * 
 * ANY PROBLEMS with values, you should start look for here!

\*******************************************************************/
void error_tracet::build_goto_trace (
  smt_partitioning_target_equationt &target,
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
       SSA_step.assignment_type==symex_target_equationt::assignment_typet::HIDDEN)
      continue;

    std::string str(SSA_step.ssa_lhs.get("identifier").c_str());
    if (is_cprover_rounding_mode_var(str))
    	continue;
    
    if (is_cprover_builtins_var(str))
    	continue;

    if (str.find(DYNAMIC_OBJ)!=std::string::npos)
        continue;
    
    if(SSA_step.ssa_lhs.id()==ID_symbol &&
       str.find(FUNC_RETURN)!=std::string::npos)
        continue;
    
    if (str.find(UNSUPPORTED_VAR_NAME) != std::string::npos)
        continue;

    if (SSA_step.ssa_lhs.get(ID_type)==ID_array)
        continue;

    step_nr++;

    goto_trace.steps.push_back(goto_trace_stept());
    goto_trace_stept &goto_trace_step=goto_trace.steps.back();

    goto_trace_step.thread_nr=SSA_step.source.thread_nr;
    goto_trace_step.pc=SSA_step.source.pc;
    goto_trace_step.comment=SSA_step.comment;
    goto_trace_step.type=SSA_step.type;
    goto_trace_step.hidden=SSA_step.hidden;
    goto_trace_step.step_nr=step_nr;
    goto_trace_step.format_string=SSA_step.format_string;
    goto_trace_step.io_id=SSA_step.io_id;
    goto_trace_step.formatted=SSA_step.formatted;
    goto_trace_step.identifier=SSA_step.identifier;
    
    if(SSA_step.ssa_lhs.is_not_nil()) {
        if (str.find(GOTO_GUARD) == 0){
            goto_trace_step.lhs_object=SSA_step.ssa_lhs;
        } else {
            //goto_trace_step.lhs_object=SSA_step.original_lhs_object;
            goto_trace_step.lhs_object=ssa_exprt(SSA_step.ssa_lhs.get_original_expr());
        }
    } else {
        goto_trace_step.lhs_object.make_nil();
    }

    if(SSA_step.ssa_full_lhs.is_not_nil())
    {
    	exprt val;
        if(is_index_member_symbol(SSA_step.ssa_full_lhs)){
            val=decider.get_value(SSA_step.ssa_full_lhs);
        }
        else {
            val=decider.get_value(SSA_step.ssa_lhs);
        }
        goto_trace_step.full_lhs_value=val;

    }
    
    /* Print nice return value info */
    if (str.find(FUNC_RETURN) < str.size() ||
        str.find(TMP_FUNC_RETURN) < str.size())
    {
        goto_trace_step.format_string = "function return value";
    } else {
        goto_trace_step.format_string=SSA_step.format_string;
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

/**
 * LRA-version of the CE-formula (obsolete).
 * analogous to the CUF-version (see next method)
 * used for debugging / comparison with CUF-version
 * (not in the theory-refinement algorithm)
 */
void error_tracet::build_goto_trace_formula (
  smt_partitioning_target_equationt &target,
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
    const symex_target_equationt::SSA_stept &SSA_step=**it;

    if(!decider.is_assignemt_true(SSA_step.guard_literal))
      continue;

    if(SSA_step.is_assignment() &&
       SSA_step.assignment_type==symex_target_equationt::assignment_typet::HIDDEN)
      continue;

    std::string str(SSA_step.ssa_lhs.get("identifier").c_str());
    if (is_cprover_rounding_mode_var(str))
    	continue;
    
    if (is_cprover_builtins_var(str))
    	continue;

    if (str.find(DYNAMIC_OBJ)!=std::string::npos)
        continue;
    
    if(SSA_step.ssa_lhs.id()==ID_symbol &&
       str.find(FUNC_RETURN)!=std::string::npos)
        continue;
    
    
    if (str.find(UNSUPPORTED_VAR_NAME) != std::string::npos)
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
          non_interp_classes[val_val]->push_back(decider2.convert(SSA_step.ssa_lhs));
          continue;
        } else if (val.get(ID_value) == "1"){
          ltr = decider2.const_var(true);
        } else if (val.get(ID_value) == "0"){
          ltr = decider2.const_var(false);
        } else {
          continue;
        }

	decider2.set_equal(ltr, decider2.convert(SSA_step.ssa_lhs));
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
  cout << "CE-formula constructed\n";
}

/**
 * CUF-version of the CE-formula
 * used in the theory-refinement algorithm
 */
void error_tracet::build_goto_trace_formula (
  std::vector<exprt>& exprs,
  std::map<const exprt, int>& model,
  smtcheck_opensmt2t &decider)
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
        exprt val = decider.get_value(*it);

        const irep_idt val_val = val.get(ID_value);
        if (val_val.size() == 0) continue;

        int ptr;
        if (val_val[0] == 'n'){
            ptr = atoi(val_val.c_str() + 1);
		    // store the max value among n-values (will be used after the loop):
            if (ptr > max_interp_value) max_interp_value = ptr;
        } else if (val_val[0] == 'a'){
            ptr = 777; // value just for fun
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
    for (std::map<const irep_idt, std::vector<exprt>*>::iterator
              it=non_interp_classes.begin(); it!=non_interp_classes.end(); ++it){
        int l1 = ++max_interp_value;
        for (unsigned int i = 0; i < it->second->size(); i++){
            model[it->second->at(i)] = l1;
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
error_tracet::isOverAppoxt error_tracet::is_trace_overapprox(smtcheck_opensmt2t &decider)
{
    /* Basic print of the error trace as all variables values */
#ifdef TRACE_DEBUG
    MainSolver *mainSolver = decider.getMainSolver();
#endif
    if (decider.has_unsupported_vars() && !decider.has_unsupported_info()) 
    // KE: only if we used any unsupported var checks and only if we didn't 
    // try to refine these expr - Need to find a better solution 
    {
        Logic *logic = decider.getLogic();
        std::set<PTRef>* vars = decider.getVars();
        //std::string overapprox_str (smtcheck_opensmt2t::_unsupported_var_str);
        //std::string skip_debug_print ("hifrog::?call"); // Skip the print of this value due to assertion
        // violation in opensmt2 - worth debuging one day: Cnfizer.C:891: lbool Cnfizer::getTermValue(PTRef) const: Assertion `val != (lbool((uint8_t)2))' failed.
        for(std::set<PTRef>::iterator iter = vars->begin(); iter != vars->end(); iter++)
        {
            // Print the var and its value
            char* name = logic->printTerm(*iter);
            std::string curr (name);
            if (curr.find(UNSUPPORTED_VAR_NAME) != std::string::npos)
                isOverAppox = error_tracet::isOverAppoxt::SPURIOUS;
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
    }
    
    if (isOverAppox != error_tracet::isOverAppoxt::SPURIOUS)
    	isOverAppox = error_tracet::isOverAppoxt::REAL;

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
    assert (isOverAppox != error_tracet::isOverAppoxt::UNKNOWN);
    
    //if (is_trace_overapprox(decider)) {
    if (isOverAppox == error_tracet::isOverAppoxt::SPURIOUS) {
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
              break;

            case goto_trace_stept::typet::ASSERT:
                if(!it->cond_value)
                {
                    out << std::endl;
                    cout << "Violated assertion at:\n" <<
                    "  file \"" << it->pc->source_location.get_file() <<
                    "\",\n  function \"" << it->pc->source_location.get_function() <<
                    "\",\n  line " << it->pc->source_location.get_line() << ":\n  " <<
                    from_expr(ns, "", it->pc->guard) << "\n";

                    out << std::endl;
                }
                break;

            case goto_trace_stept::typet::ASSIGNMENT:
                if(it->pc->is_assign() ||
                        it->pc->is_return() || // returns have a lhs!
                        it->pc->is_function_call() ||
                        (it->pc->is_other() && it->lhs_object.is_not_nil()))
                {
                    if(prev_step_nr!=it->step_nr || first_step)
                    {
                        first_step=false;
                        prev_step_nr=it->step_nr;
                        show_state_header(out, it->thread_nr, it->pc->source_location, it->step_nr);
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

            case goto_trace_stept::typet::OUTPUT:
                if(it->formatted)
                {
                    printf_formattert printf_formatter(ns);
                    printf_formatter(id2string(it->format_string), it->io_args);
                    printf_formatter.print(out);
                    out << std::endl;
                }
                else
                {
                    show_state_header(out, it->thread_nr, it->pc->source_location, it->step_nr);
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

            case goto_trace_stept::typet::INPUT:
                show_state_header(out, it->thread_nr, it->pc->source_location, it->step_nr);
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
                //std::cout << "Error " << it->type << std::endl;
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
  const source_locationt &location,
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

/*******************************************************************\

Function: error_trace::build_exec_order_goto_trace - for NO PARTITON VERISION

  Inputs: SSA translation of the code and solver

 Outputs: a concrete trace (error trace with value)

 Purpose: To create a concrete error trace with concrete values

 Note: Copied from build_goto_tarce.cpp
 * 
 * ANY PROBLEMS with values, you should start look for here!

\*******************************************************************/
void error_tracet::build_goto_trace (
  smt_symex_target_equationt &target,
  smtcheck_opensmt2t &decider)
{

  unsigned step_nr=0;

  for(symex_target_equationt::SSA_stepst::iterator
      it=target.SSA_steps.begin();
      it!=target.SSA_steps.end();
      it++)
  {
    const symex_target_equationt::SSA_stept &SSA_step=(*it);
    if(!decider.is_assignemt_true(SSA_step.guard_literal))
      continue;

    if(SSA_step.is_assignment() &&
       SSA_step.assignment_type==symex_target_equationt::assignment_typet::HIDDEN)
      continue;

    std::string str(SSA_step.ssa_lhs.get("identifier").c_str());
    if (is_cprover_rounding_mode_var(str))
    	continue;
    
    if (is_cprover_builtins_var(str))
    	continue;

    if (str.find(DYNAMIC_OBJ)!=std::string::npos)
        continue;
    
    if(SSA_step.ssa_lhs.id()==ID_symbol &&
       str.find(FUNC_RETURN)!=std::string::npos)
        continue;
    
    if (str.find(UNSUPPORTED_VAR_NAME) != std::string::npos)
        continue;

    if (SSA_step.ssa_lhs.get(ID_type)==ID_array)
        continue;

    step_nr++;

    goto_trace.steps.push_back(goto_trace_stept());
    goto_trace_stept &goto_trace_step=goto_trace.steps.back();

    goto_trace_step.thread_nr=SSA_step.source.thread_nr;
    goto_trace_step.pc=SSA_step.source.pc;
    goto_trace_step.comment=SSA_step.comment;
    goto_trace_step.type=SSA_step.type;
    goto_trace_step.hidden=SSA_step.hidden;
    goto_trace_step.step_nr=step_nr;
    goto_trace_step.format_string=SSA_step.format_string;
    goto_trace_step.io_id=SSA_step.io_id;
    goto_trace_step.formatted=SSA_step.formatted;
    goto_trace_step.identifier=SSA_step.identifier;
    
    if(SSA_step.ssa_lhs.is_not_nil()) {
        if (str.find(GOTO_GUARD) == 0){
            goto_trace_step.lhs_object=SSA_step.ssa_lhs;
        } else {
            //goto_trace_step.lhs_object=SSA_step.original_lhs_object;
            goto_trace_step.lhs_object=ssa_exprt(SSA_step.ssa_lhs.get_original_expr());
        }
    } else {
        goto_trace_step.lhs_object.make_nil();
    }

    if(SSA_step.ssa_full_lhs.is_not_nil())
    {
    	exprt val;
        if(is_index_member_symbol(SSA_step.ssa_full_lhs)){
            val=decider.get_value(SSA_step.ssa_full_lhs);
        }
        else {
            val=decider.get_value(SSA_step.ssa_lhs);
        }
        goto_trace_step.full_lhs_value=val;

    }
    
    /* Print nice return value info */
    if (str.find(FUNC_RETURN) < str.size() ||
	str.find(TMP_FUNC_RETURN) < str.size())
    {
        goto_trace_step.format_string = "function return value";
    } else {
        goto_trace_step.format_string=SSA_step.format_string;
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
