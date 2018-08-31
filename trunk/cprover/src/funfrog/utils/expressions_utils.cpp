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
