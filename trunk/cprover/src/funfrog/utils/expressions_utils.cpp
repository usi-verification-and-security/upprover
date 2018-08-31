//
// Created by Martin Blicha on 24.08.18.
//

#include "expressions_utils.h"

void getVarsInExpr(exprt & e, std::set<exprt> & vars) {
    if (e.id() == ID_symbol) {
        if (is_cprover_builtins_var(e)) {
            // Skip rounding_mode or any other builtins vars
        } else {
            vars.insert(e);
        }
    } else if (e.has_operands()) {
        for (unsigned int i = 0; i < e.operands().size(); i++) {
            getVarsInExpr(e.operands()[i], vars);
        }
    }
}


/*******************************************************************\

Function: create_bound_string

 Inputs: 

 Outputs: 

 Purpose: for type constraints of CUF and LRA
 * Was part of smtcheck_opensmt2t originally

\*******************************************************************/
std::string create_bound_string(std::string base, int exp)
{
    std::string ret = base;
    int size = exp - base.size() + 1; // for format 3.444444
    for (int i=0; i<size;i++)
        ret+= "0";

    return ret;
}

// Indicate if assignment shall be skip in non-prop mode.
bool is_cprover_builtins_prop_eq(const exprt &expr, const std::string logic)
{
    if (logic == "prop")
        return false;
    
    // If not prop, shall skip all such equations!
    if (!expr.has_operands())
        return false;
    if (expr.operands().size() > 2)
        return false;
    // Start checking if it is auto gen code for rounding model
    std::string str = id2string((expr.operands()[0]).get(ID_identifier));
    if (is_cprover_builtins_var(str))
        return true;
    if (expr.id() == ID_typecast || expr.id() == ID_floatbv_typecast) {
        if (is_cprover_builtins_prop_eq(expr.operands()[0],logic)) return true;
    }
    
    if (expr.operands().size() < 2) return false;
    
    str = id2string((expr.operands()[1]).get(ID_identifier));
    if (is_cprover_builtins_var(str))
        return true;
    return false;
}
