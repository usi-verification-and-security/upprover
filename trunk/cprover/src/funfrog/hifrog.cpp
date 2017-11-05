#include "hifrog.h"
#include <string.h>
#include <algorithm>
//#include <iostream> // Comment only for debug

/* Get the name of an SSA expression without the instance number 
 *    
 * KE: please use it, as cprover framework keeps changing all the time
 */
irep_idt get_symbol_name(const exprt &expr) {
    // FIXME: everything except the last return line should be removed when we clear the problems with naming conventions
    // KE: need to use fabricate symbol in produce_callsite_symbols in symex_assertion_sum
    if (is_hifrog_inner_symbol_name(expr)) {
        return extract_hifrog_inner_symbol_name(expr);
    }
    //std::cout << "Get symbol name called for:\n" << expr.pretty() << '\n';
    return to_ssa_expr(expr).get_original_name();
}

irep_idt get_symbol_L1_name(const exprt &expr) {
    if (is_hifrog_inner_symbol_name(expr))
        return extract_hifrog_inner_symbol_name(expr);
    
    return to_ssa_expr(expr).get_l1_object_identifier();
}

bool is_hifrog_inner_symbol_name(const exprt &expr) {
    std::string test4inned_hifrog = id2string(expr.get(ID_identifier));
    if (test4inned_hifrog.find(CALLSTART_SYMBOL) != std::string::npos)
        return true;
    if (test4inned_hifrog.find(CALLEND_SYMBOL) != std::string::npos)
        return true;
    if (test4inned_hifrog.find(ERROR_SYMBOL) != std::string::npos)
        return true;
 
    return false;
}

irep_idt extract_hifrog_inner_symbol_name(const exprt &expr){
    std::string test4inned_hifrog = id2string(expr.get(ID_identifier));
    
    size_t pos = test4inned_hifrog.find(FUNC_RETURN);
    if (pos != std::string::npos)
        return test4inned_hifrog.substr(0,pos) + FUNC_RETURN;
    
    pos = test4inned_hifrog.find(TMP_FUNC_RETURN);
    if (pos != std::string::npos)
        return test4inned_hifrog.substr(0,pos) + TMP_FUNC_RETURN;
    
    if (test4inned_hifrog.find(CALLSTART_SYMBOL) != std::string::npos)
        return CALLSTART_SYMBOL;
    if (test4inned_hifrog.find(CALLEND_SYMBOL) != std::string::npos)
        return CALLEND_SYMBOL;   
    if (test4inned_hifrog.find(ERROR_SYMBOL) != std::string::npos)
        return ERROR_SYMBOL;
 
//    assert(0); // Add constants if needed
    throw std::logic_error("Unknown symbol encountered!");
}

unsigned get_symbol_L2_counter(const exprt &expr) {
    if (is_hifrog_inner_symbol_name(expr))
        return extract_hifrog_inner_symbol_L2_counter(expr);
    
    return atoi(to_ssa_expr(expr).get_level_2().c_str());
}

unsigned extract_hifrog_inner_symbol_L2_counter(const exprt &expr){
    std::string test4inned_hifrog = id2string(expr.get(ID_identifier));
    size_t pos = extract_hifrog_inner_symbol_name(expr).size();
    if ((test4inned_hifrog.find(CALLSTART_SYMBOL) != std::string::npos) ||
        (test4inned_hifrog.find(CALLEND_SYMBOL) != std::string::npos) ||
        (test4inned_hifrog.find(ERROR_SYMBOL) != std::string::npos))
        return atoi(test4inned_hifrog.substr(pos+1).c_str());

    throw std::logic_error("Unknown symbol encountered!");
    //assert(0); // Add constants if needed
}

/* Assure the name is always symex::nondet#number */
std::string fix_symex_nondet_name(const exprt &expr) {
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
    
    return name_expr;
}

bool is_cprover_initialize_method(const std::string & name) {
    return name == INITIALIZE;
}