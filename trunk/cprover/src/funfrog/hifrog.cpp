#include "hifrog.h"
#include <algorithm>
#include "utils/naming_helpers.h"

/* Get the name of an SSA expression without the instance number 
 *    
 * KE: please use it, as cprover framework keeps changing all the time
 */
irep_idt get_symbol_name(const exprt &expr) {
    //std::cout << "Get symbol name called for:\n" << expr.pretty() << '\n';
    return to_ssa_expr(expr).get_original_name();
}

/* Assure the name is always symex::nondet#number */
std::string normalize_name(const exprt &expr) {
    // Fix Variable name - sometimes "nondet" name is missing, add it for these cases
    
    std::string name_expr = id2string(expr.get(ID_identifier));
    assert (name_expr.size() != 0); // Check the we really got something
    if (expr.id() == ID_nondet_symbol)
    {
        if (name_expr.find(NONDETv2) != std::string::npos) {
            name_expr = name_expr.insert(13,1, '#');
        } else if (name_expr.find(NONDETv1) != std::string::npos) {
            name_expr = name_expr.insert(7, SYMEX_NONDET);
        }  
    }
       
    name_expr.erase(std::remove(name_expr.begin(),name_expr.end(),'\\'),name_expr.end());

    return name_expr;
}

// Get a unique index per query's dump
unsigned int get_dump_current_index()
{
    static unsigned int index=0;
    index+=1;
    return index;
}

// Test if name is without L2 level
bool is_L2_SSA_symbol(const exprt& expr)
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

// For CUF algorithm - helper to extract CEX
void getVarsInExpr(exprt& e, std::set<exprt>& vars)
{
    if(e.id()==ID_symbol){
        if (is_cprover_builtins_var(e))
        {
            // Skip rounding_mode or any other builtins vars
        }
        else
        {
            vars.insert(e);
        }
    } else if (e.has_operands()){
        for (unsigned int i = 0; i < e.operands().size(); i++){
            getVarsInExpr(e.operands()[i], vars);
        }
    }
}

/*******************************************************************\

Function: extract_expr_str_number

  Inputs: expression that is a constant (+/-/int/float/rational)

 Outputs: a string of the number

 Purpose: assure we are extracting the number correctly.

 expr.get(ID_C_cformat).c_str() - doesn't work for negative numbers!
 * And thanks god (the starts and mother nature) that this option 
 * is NOT in new Cprover framework

\*******************************************************************/
std::string extract_expr_str_number(const exprt &expr)
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
    
    // Special cases for eNum in Cprover
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
        // TODO: add more cases if the asesrt below fails!
    }
    assert(const_val.size() > 0);

    return const_val;
}
