//
// Created by Martin Blicha on 05.08.18.
//

#ifndef PROJECT_EXPRESSIONS_UTILS_H
#define PROJECT_EXPRESSIONS_UTILS_H

#include <util/expr.h>

inline bool is_boolean(const exprt & expr){
    return expr.is_boolean() || expr.type().id() == ID_c_bool;
}

inline bool is_symbol(const exprt & expr) {
    return expr.id() == ID_symbol;
}

inline bool is_ssa_symbol(const exprt & expr) {
    return is_symbol(expr) && expr.get_bool(ID_C_SSA_symbol);
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
    std::string const_val = expr.print_number_2smt(); // DO NOT CHANGE TO cprover util code as it works only for positive or unsigned!
    //(unless upgrade, please keep the checks/assert!)
    // If can be that we missed more cases... use the debug prints to check conversions!!
#ifdef DEBUG_SSA_SMT_NUMERIC_CONV
    std::cout << "; EXTRACTING NUMBER " << const_val
            << " (ORIG-EXPR " << expr.get(ID_value)
            << " :: " << expr.type().id() << ")" << endl;
    //std::cout << "; TEST FOR EXP C FORMAT GIVES " << expr.get(ID_C_cformat).c_str() << " with TYPE " << expr.type().id_string() << endl;
#endif
    return const_val;
}

#endif //PROJECT_EXPRESSIONS_UTILS_H
