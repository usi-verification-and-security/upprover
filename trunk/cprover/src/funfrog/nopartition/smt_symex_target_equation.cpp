/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

/* 
 * File:   smt_symex_target_equationt.cpp
 * Author: karinek
 * 
 * Created on 21 April 2017, 11:33
 */

#include "smt_symex_target_equation.h"

void smt_symex_target_equationt::convert(smtcheck_opensmt2t &decider) 
{
  // Open a single partition 
  decider.new_partition();

  // Do convert to all program at once
  convert_guards(decider);
  convert_assignments(decider);
  //convert_decls(decider);
  convert_assumptions(decider);
  convert_assertions(decider);
  convert_goto_instructions(decider);
  convert_io(decider);
  //convert_constraints(decider);
  convert_summary(decider);
  
  // KE: not sure we are not suppose to add all these to the flow
}

// Convert a specific partition guards of SSA steps - GUARD-OUT
void smt_symex_target_equationt::convert_guards(smtcheck_opensmt2t &decider)
{
    for(auto &step : SSA_steps) {
        if (step.ignore) {
#       ifdef DEBUG_SSA_SMT_CALL
            cout << "Before decider::const_var(GUARD-OUT) --> false" << endl;
#       endif
            step.guard_literal = decider.const_var(false);
        } else {
            exprt tmp(step.guard);
#       ifdef DEBUG_SSA_PRINT
            expr_ssa_print_guard(out_terms, tmp, partition_smt_decl);
            if (!tmp.is_boolean())
                terms_counter++; // SSA -> SMT shall be all in a new function
#       endif
#       ifdef DEBUG_SSA_SMT_CALL
            expr_ssa_print_smt_dbg(
                cout << "Before decider::convert(GUARD-OUT) --> ", tmp,false);
#	endif
            step.guard_literal = decider.convert(tmp);
        }
    }      
}

// Convert a specific partition assignments of SSA steps
void smt_symex_target_equationt::convert_assignments(smtcheck_opensmt2t &decider)
{
    for(auto &step : SSA_steps) {
        if (step.is_assignment() && !step.ignore) {
            exprt tmp(step.cond_expr);

            // Only if not an assignment to rounding model print it + add it to LRA statements
            if (!isRoundModelEq(tmp)) {
#           ifdef DEBUG_SSA_PRINT
                expr_ssa_print(out_terms << "    ", tmp, partition_smt_decl, false);
                terms_counter++;
#           endif
#           ifdef DEBUG_SSA_SMT_CALL
                expr_ssa_print_smt_dbg(
                cout << "Before decider::set_to_true(ASSIGN-OUT) --> ", tmp, false);
#           endif
                decider.set_to_true(tmp);
                exprs.push_back(tmp);
            }
        }
        
    }
}

// Convert a specific partition assumptions of SSA steps
void smt_symex_target_equationt::convert_assumptions(smtcheck_opensmt2t &decider)
{
    for(auto &step : SSA_steps) {
        if (step.is_assume()) {
            if (step.ignore) {
#           ifdef DEBUG_SSA_SMT_CALL
                cout << "Before decider::const_var(ASSUME-OUT) --> true" << endl;
#           endif
                step.cond_literal = decider.const_var(true);
                // GF
            } else {
                exprt tmp(step.cond_expr);
#               ifdef DEBUG_SSA_SMT_CALL
                    expr_ssa_print_smt_dbg(
                            cout << "Before decider::convert(ASSUME-OUT) --> ",
                            tmp, false);
#               endif
                step.cond_literal = decider.convert(tmp);
            }
        }
    }
}

// Convert a specific partition assumptions of SSA steps
void smt_symex_target_equationt::convert_goto_instructions(smtcheck_opensmt2t &decider)
{
    for(auto &step : SSA_steps) {
        if (step.is_goto()) {
            if (step.ignore) {
#           ifdef DEBUG_SSA_SMT_CALL
                cout << "Before decider::const_var(GOTO-OUT) --> true" << endl;
#           endif
                step.cond_literal = decider.const_var(true);
                // GF
            } else {
                exprt tmp(step.cond_expr);
#               ifdef DEBUG_SSA_SMT_CALL
                    expr_ssa_print_smt_dbg(
                            cout << "Before decider::convert(GOTO-OUT) --> ",
                            tmp, false);
#               endif
                step.cond_literal = decider.convert(tmp);
            }
        }
    }
}

// Convert a specific partition assertions of SSA steps
void smt_symex_target_equationt::convert_assertions(smtcheck_opensmt2t &decider)
{   
    unsigned number_of_assertions=count_assertions();
    if(number_of_assertions==0) return;

#ifdef DEBUG_SSA_SMT_CALL
    cout << "Before decider::const_var(ASSERT-OUT) --> true" << endl;
#endif

    if(number_of_assertions==1)
    {
        for(auto &step : SSA_steps)
        {
            if(step.is_assert())
            {
                decider.set_to_false(step.cond_expr);
                //step.cond_literal=const_literal(false);
                step.cond_literal = decider.const_var(false);
                return; // prevent further assumptions!
            }
            else if(step.is_assume())
                decider.set_to_true(step.cond_expr);
        }

        assert(false); // unreachable
    }

    // We do (NOT a1) OR (NOT a2) ...
    // where the a's are the assertions
    or_exprt::operandst disjuncts;
    disjuncts.reserve(number_of_assertions);

    exprt assumption=true_exprt();

    for(auto &step : SSA_steps)
    {
        if(step.is_assert())
        {
            implies_exprt implication(
                    assumption,
                    step.cond_expr);

            // do the conversion
            step.cond_literal=decider.convert(implication);

            // store disjunct
            disjuncts.push_back(literal_exprt(!step.cond_literal));
        }
        else if(step.is_assume())
        {
            // the assumptions have been converted before
            // avoid deep nesting of ID_and expressions
            if(assumption.id()==ID_and)
                assumption.copy_to_operands(literal_exprt(step.cond_literal));
            else
                assumption=
                    and_exprt(assumption, literal_exprt(step.cond_literal));
        }
    }

    // the below is 'true' if there are no assertions
    decider.set_to_true(disjunction(disjuncts));
}

// Convert a specific partition io of SSA steps
void smt_symex_target_equationt::convert_io(smtcheck_opensmt2t &decider)
{
    for(auto &step : SSA_steps) {
        if (!step.ignore) {
            for (std::list<exprt>::const_iterator o_it = step.io_args.begin(); o_it
                            != step.io_args.end(); ++o_it) {
                exprt tmp = *o_it;
                if (tmp.is_constant() || tmp.id() == ID_string_constant)
                    step.converted_io_args.push_back(tmp);
                else {
                    symbol_exprt symbol(("symex::io::"+std::to_string(io_count_global++)), tmp.type());

#ifdef DEBUG_SSA_SMT_CALL
                    expr_ssa_print_smt_dbg(cout << "Before decider::set_to_true --> ",
                        equal_exprt(tmp, symbol), false);
#endif
                    decider.set_to_true(equal_exprt(tmp, symbol));
                    step.converted_io_args.push_back(symbol);
                }
            }
        }

    }    
}

// Convert a summary partition (i.e., assert its summary)
void smt_symex_target_equationt::convert_summary(smtcheck_opensmt2t &decider)
{
    // TODO: if we extands this version to general cbmc with summaries, 
    // then we need to implement this method    
    
    //bool is_summary;
    //if (!is_summary) return;
}

bool smt_symex_target_equationt::isRoundModelEq(const exprt &expr) 
{
    if (!expr.has_operands())
        return false;
    if (expr.operands().size() > 2)
        return false;

    // Start checking if it is auto gen code for rounding model
    string str = id2string((expr.operands()[0]).get(ID_identifier));
    if (str.find("__CPROVER_") != std::string::npos)
        return true;
    
    if (expr.operands().size() < 2) return false;
    
    str = id2string((expr.operands()[1]).get(ID_identifier));
    if (str.find("__CPROVER_") != std::string::npos)
        return true;

    return false;
}