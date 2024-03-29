/********************************************************************
 * File:   hifrog_symex_target_equationt_no_partition.cpp
 * Author: karinek
 * Created on 21 April 2017
 ********************************************************************/

#include "hifrog_symex_target_equation_no_partition.h"
#include "funfrog/utils/expressions_utils.h"
#include <solvers/prop/literal_expr.h>
#include "../utils/naming_helpers.h"
#include <funfrog/interface/convertor.h>


#ifdef DISABLE_OPTIMIZATIONS
#include <fstream>
using namespace std;

#include "../expr_pretty_print.h"
#endif

void hifrog_symex_target_equationt::convert(convertort &convertor)
{
  // Do convert to all program at once
  convert_guards(convertor);
  convert_assignments(convertor);
  //convert_decls(decider);
  convert_assumptions(convertor);
  convert_assertions(convertor);
  convert_goto_instructions(convertor);
  convert_io(convertor);
  convert_constraints(convertor);
  convert_summary(convertor);
  
#ifdef DISABLE_OPTIMIZATIONS
  if (dump_SSA_tree)
  {
    ofstream out_ssaT;
    out_ssaT.open(ssa_tree_file_name+"_"+std::to_string(get_unique_index())+".smt2");
  
    // Print all after the headers: decl and code
    print_partition();
    print_all_partition(out_ssaT);
    
    out_ssaT.close();
  }
#endif
  
  // KE: not sure we are not suppose to add all these to the flow
}

// Convert a specific partition guards of SSA steps - GUARD-OUT
void hifrog_symex_target_equationt::convert_guards(convertort &convertor)
{
    for(auto &step : SSA_steps) {
        if (step.ignore) {
#       ifdef DEBUG_SSA_SMT_CALL
            cout << "Before decider::const_var(GUARD-OUT) --> false" << endl;
#       endif
            step.guard_literal = flaref_to_literal(convertor.get_const_literal(false));
            //step.guard_handle = false_exprt();
        } else {
            exprt tmp(step.guard);
#       ifdef DISABLE_OPTIMIZATIONS
            expr_ssa_print_guard(out_terms, tmp, partition_smt_decl);
            if (!tmp.is_boolean())
                terms_counter++; // SSA -> SMT shall be all in a new function
#       endif
#       if defined(DEBUG_SSA_SMT_CALL) && defined(DISABLE_OPTIMIZATIONS)
            expr_ssa_print_smt_dbg(
                cout << "Before decider::convert(GUARD-OUT) --> ", tmp,false);
#	endif
            step.guard_literal = flaref_to_literal(convertor.convert_bool_expr(tmp));
            //step.guard_handle = tmp;
        }
    }      
}

// Convert a specific partition assignments of SSA steps
void hifrog_symex_target_equationt::convert_assignments(convertort &convertor)
{
    for(auto &step : SSA_steps) {
        if (step.is_assignment() && !step.ignore) {
            exprt tmp(step.cond_expr);

            // Only if not an assignment to rounding model print it + add it to LRA statements
            if (!isPropBuiltinEq(tmp)) {
#           ifdef DISABLE_OPTIMIZATIONS
                expr_ssa_print(out_terms << "    ", tmp, partition_smt_decl, false);
                terms_counter++;
#             ifdef DEBUG_SSA_SMT_CALL
                expr_ssa_print_smt_dbg(
                cout << "Before decider::set_to_true(ASSIGN-OUT) --> ", tmp, false);
#             endif
#           endif                
                convertor.set_to_true(tmp);
                exprs.push_back(tmp);
            }
        }
        
    }
}

void hifrog_symex_target_equationt::convert_constraints(convertort &convertor) const
{
  for(const auto &step : SSA_steps)
  {
    if(step.is_constraint())
    {
      if(step.ignore)
        continue;

      convertor.set_to_true(step.cond_expr);
    }
  }
}

// Convert a specific partition assumptions of SSA steps
void hifrog_symex_target_equationt::convert_assumptions(convertort &convertor)
{
    for(auto &step : SSA_steps) {
        if (step.is_assume()) {
            if (step.ignore) {
#           ifdef DEBUG_SSA_SMT_CALL
                cout << "Before decider::const_var(ASSUME-OUT) --> true" << endl;
#           endif
                step.cond_literal = flaref_to_literal(convertor.get_const_literal(true));
                //step.cond_handle = true_exprt();
                // GF
            } else {
                exprt tmp(step.cond_expr);
#               if defined(DEBUG_SSA_SMT_CALL) && defined(DISABLE_OPTIMIZATIONS)
                    expr_ssa_print_smt_dbg(
                            cout << "Before decider::convert(ASSUME-OUT) --> ",
                            tmp, false);
#               endif
                step.cond_literal = flaref_to_literal(convertor.convert_bool_expr(tmp));
                //step.cond_handle = tmp;
            }
        }
    }
}

// Convert a specific partition assumptions of SSA steps
void hifrog_symex_target_equationt::convert_goto_instructions(convertort &convertor)
{
    for(auto &step : SSA_steps) {
        if (step.is_goto()) {
            if (step.ignore) {
#           ifdef DEBUG_SSA_SMT_CALL
                cout << "Before decider::const_var(GOTO-OUT) --> true" << endl;
#           endif
                step.cond_literal = flaref_to_literal(convertor.get_const_literal(true));
                //step.cond_handle = true_exprt();
            } else {
                exprt tmp(step.cond_expr);
#               if defined(DEBUG_SSA_SMT_CALL) && defined(DISABLE_OPTIMIZATIONS)
                    expr_ssa_print_smt_dbg(
                            cout << "Before decider::convert(GOTO-OUT) --> ",
                            tmp, false);
#               endif
                step.cond_literal = flaref_to_literal(convertor.convert_bool_expr(tmp));
                //step.cond_handle = tmp;
            }
        }
    }
}

// Convert a specific partition assertions of SSA steps
void hifrog_symex_target_equationt::convert_assertions(convertort &convertor)
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
                convertor.set_to_false(step.cond_expr);
                //step.cond_literal=const_literal(false);
                step.cond_literal = flaref_to_literal(convertor.get_const_literal(false));
                //step.cond_handle = false_exprt();
                return; // prevent further assumptions!
            }
            else if(step.is_assume())
                convertor.set_to_true(step.cond_expr);
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
            step.cond_literal = flaref_to_literal(convertor.convert_bool_expr(implication));
            //step.cond_handle = implication;
            // store disjunct
            disjuncts.push_back(literal_exprt(!step.cond_literal));
            //disjuncts.push_back(not_exprt(step.cond_handle));
        }
        else if(step.is_assume())
        {
            // the assumptions have been converted before
            // avoid deep nesting of ID_and expressions
//            if(assumption.id()==ID_and)
//                //assumption.copy_to_operands(step.cond_handle);
//            else
//                assumption=
//                    and_exprt(assumption, step.cond_handle);
            if(assumption.id()==ID_and)
                assumption.copy_to_operands(literal_exprt(step.cond_literal));
            else
                assumption=
                        and_exprt(assumption, literal_exprt(step.cond_literal));
        }

    }

    // the below is 'true' if there are no assertions
    convertor.set_to_true(disjunction(disjuncts));
}

// Convert a specific partition io of SSA steps
void hifrog_symex_target_equationt::convert_io(convertort &convertor)
{
    for(auto &step : SSA_steps) {
        if (!step.ignore) {
            for (std::list<exprt>::const_iterator o_it = step.io_args.begin(); o_it
                            != step.io_args.end(); ++o_it) {
                exprt tmp = *o_it;
                if (tmp.is_constant() || tmp.id() == ID_string_constant)
                    step.converted_io_args.push_back(tmp);
                else {
                    symbol_exprt symbol((CProverStringConstants::IO_CONST + std::to_string(io_count_global++)), tmp.type());

#if defined(DEBUG_SSA_SMT_CALL) && defined(DISABLE_OPTIMIZATIONS)
                    expr_ssa_print_smt_dbg(cout << "Before decider::set_to_true --> ",
                        equal_exprt(tmp, symbol), false);
#endif
                    convertor.set_to_true(equal_exprt(tmp, symbol));
                    step.converted_io_args.push_back(symbol);
                }
            }
        }

    }    
}

// Convert a summary partition (i.e., assert its summary)
void hifrog_symex_target_equationt::convert_summary(convertort &convertor)
{
    // TODO: if we extands this version to general cbmc with summaries, 
    // then we need to implement this method    
    
    //bool is_summary;
    //if (!is_summary) return;
}

bool hifrog_symex_target_equationt::isPropBuiltinEq(const exprt &expr)
{
    if (!expr.has_operands())
        return false;
    if (expr.operands().size() > 2)
        return false;

    // Start checking if it is auto gen code for rounding model
    if (is_cprover_builtins_var((expr.operands()[0]))) return true;
    if (expr.operands().size() < 2) return false;
    if (is_cprover_builtins_var((expr.operands()[1]))) return true;

    return false;
}

#ifdef DISABLE_OPTIMIZATIONS
std::ostream& hifrog_symex_target_equationt::print_decl_smt(std::ostream& out) {
    if (partition_smt_decl->empty())
        return out;
    else {
        // Print all decl
        for (std::map<std::string, exprt>::iterator it =
                        partition_smt_decl->begin(); it != partition_smt_decl->end(); ++it) {
            out << "(declare-fun " << it->first << ")" << std::endl;
        }

        // At the end of the loop
        partition_smt_decl->clear(); //Ready for the next partition
        return out;
    }
}

void hifrog_symex_target_equationt::print_partition() {
    // When creating the real formula - do not add the assert here, check first if OpenSMT2 does it
    out_partition << "; " << basic_buf.str();
    if (terms_buf.str().length() > 0) {
        out_partition << "(assert\n";
        if (terms_counter > 1)
            out_partition << "  (and\n" << terms_buf.str() << "  )\n)" << endl;
        else
            out_partition << terms_buf.str() << ")" << endl;
    }

    // Init for reuse
    terms_buf.str("");
    basic_buf.str("");
    terms_counter = 0;
}

void hifrog_symex_target_equationt::print_all_partition(std::ostream& out) {
    // Print only if the flag is on!
    // Print header - not part of temp debug print!
    out << "\nXXX SSA --> SMT-lib Translation XXX\n";

    // for prints later on
    std::ostream out_decl(0);
    std::stringbuf decl_buf;
    out_decl.rdbuf(&decl_buf);

    // When creating the real formula - do not add the assert here, check first if OpenSMT2 does it
    print_decl_smt(out_decl); // print the symbol decl
    out << decl_buf.str() << partition_buf.str() << "(check-sat)\n";
}

void hifrog_symex_target_equationt::saveFirstCallExpr(const exprt& expr) {
    if (!is_first_call)
        return;
    
    is_first_call = false;
    first_call_expr = &expr;
}

bool hifrog_symex_target_equationt::isFirstCallExpr(const exprt& expr) {
    if (is_first_call)
        return false;

    //return (first_call_expr->compare(expr) != 0); // for debug
    return (first_call_expr->pretty().compare(expr.pretty()) != 0);
}
#endif
