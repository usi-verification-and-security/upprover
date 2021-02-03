//
// Created by Martin Blicha on 05.08.18.
//

#ifndef PROJECT_EXPRESSIONS_UTILS_H
#define PROJECT_EXPRESSIONS_UTILS_H

#include <util/expr.h>
#include <util/ssa_expr.h>
#include "naming_helpers.h"

#include <set>
#include <algorithm>

inline bool is_boolean(const exprt & expr){
    return expr.is_boolean() || expr.type().id() == ID_c_bool;
}

inline bool is_symbol(const exprt & expr) {
    return expr.id() == ID_symbol;
}

inline bool is_ssa_symbol(const exprt & expr) {
    return is_symbol(expr) && expr.get_bool(ID_C_SSA_symbol);
}

inline bool is_global(const exprt& expr){
    if(!expr.get_bool(ID_C_SSA_symbol)){
        return false;
    }
    return to_ssa_expr(expr).get_level_0().empty();
}

/*******************************************************************\

Function: smtcheck_opensmt2t::extract_expr_str_number

  Inputs: expression that is a constant (+/-/int/float/rational)

 Outputs: a string of the number

 Purpose: assure we are extracting the number correctly.

 expr.get(ID_C_cformat).c_str() - doesn't work for negative numbers!
 * And thanks god (the starts and mother nature) that this option
 * is NOT in new Cprover framework

\*******************************************************************/
inline std::string extract_expr_str_number(const exprt &expr)
{
    std::string const_val = expr.print_number_2smt(expr); // DO NOT CHANGE TO cprover util code as it works only for positive or unsigned!
    //(unless upgrade, please keep the checks/assert!)
    // If can be that we missed more cases... use the debug prints to check conversions!!
#ifdef DEBUG_SSA_SMT_NUMERIC_CONV
    std::cout << "; EXTRACTING NUMBER " << const_val
            << " (ORIG-EXPR " << expr.get(ID_value)
            << " :: " << expr.type().id() << ")" << endl;
    //std::cout << "; TEST FOR EXP C FORMAT GIVES " << expr.get(ID_C_cformat).c_str() << " with TYPE " << expr.type().id_string() << endl;
#endif
    
    // Fix enum:
    if(const_val.size() <= 0)
    {
        if (expr.type().id() == ID_c_enum)
        {
            const_val = expr.type().find(ID_tag).pretty();
        }
        else if (expr.type().id() == ID_c_enum_tag)
        {
            const_val = id2string(to_constant_expr(expr).get_value());
        }
    }
    
    assert(const_val.size()>0); // Must be a number
    return const_val;
}

inline bool is_cprover_rounding_mode_var(const exprt& e)
{
    return is_cprover_rounding_mode_var(id2string(e.get(ID_identifier)));
}

inline bool is_cprover_builtins_var(const exprt& e)
{
    return is_cprover_builtins_var(id2string(e.get(ID_identifier)));
}

inline irep_idt get_symbol_name(const exprt &expr) {
    //std::cout << "Get symbol name called for:\n" << expr.pretty() << '\n';
    return to_ssa_expr(expr).get_original_name();
}

inline irep_idt get_symbol_L1_name(const exprt &expr) {
    return to_ssa_expr(expr).get_l1_object_identifier();
}

// Test if name is without L2 level
inline bool is_L2_SSA_symbol(const exprt& expr)
{
    if (expr.id() == ID_nondet_symbol)
        return true; // KE: need to be tested!

    // Else check program symbols
    if (expr.id()!=ID_symbol)
        return false;
    if (!expr.get_bool(ID_C_SSA_symbol))
        return false;
    if (expr.has_operands())
        return false;
    if (expr.get(ID_identifier) == get_symbol_name(expr)){
        return false;
    }else if (expr.get(ID_identifier) == get_symbol_L1_name(expr)){
        return false;
    }

    return true;
}

inline std::string normalize_name(const exprt & expr) {
    // Fix Variable name - sometimes "nondet" name is missing, add it for these cases

    std::string name_expr = id2string(expr.get(ID_identifier));
    assert (name_expr.size() != 0); // Check the we really got something
    if (expr.id() == ID_nondet_symbol)
    {
        if (name_expr.find(CProverStringConstants::NONDETv2) != std::string::npos) {
            name_expr = name_expr.insert(13,1, '#');
        } else if (name_expr.find(CProverStringConstants::NONDETv1) != std::string::npos) {
            name_expr = name_expr.insert(7, CProverStringConstants::SYMEX_NONDET);
        }
    }

    // TODO: check if this is necessary
    name_expr.erase(std::remove(name_expr.begin(),name_expr.end(),'\\'),name_expr.end());

    return name_expr;
}

// For CUF trace
void getVarsInExpr(exprt& e, std::set<exprt>& vars);

//for type constraints of CUF and LRA
//build the string of the upper and lower bounds
std::string create_bound_string(std::string base, int exp);

// Check for lia and lra if linear operator
bool is_linear_expression(const exprt &expr);

#endif //PROJECT_EXPRESSIONS_UTILS_H
