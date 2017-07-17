#include "hifrog.h"
#include <string.h>
#include <iostream>

/* Get the name of an SSA expression without the instance number 
   
 * KE: please use it, as cprover framework keeps changeing all the time
 */
irep_idt get_symbol_name(const exprt &expr) {
    if (is_hifrog_inner_symbol_name(expr))
        return extract_hifrog_inner_symbol_name(expr);
    
    return to_ssa_expr(expr).get_l1_object_identifier();
}

bool is_hifrog_inner_symbol_name(const exprt &expr) {
    std::string test4inned_hifrog = id2string(expr.get(ID_identifier));
    if (test4inned_hifrog.find(FUNC_RETURN) != std::string::npos)
        return true;
    if (test4inned_hifrog.find(TMP_FUNC_RETURN) != std::string::npos)
        return true;
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
 
    assert(0); // Add constants if needed

}

unsigned get_symbol_L2_counter(const exprt &expr) {
    if (is_hifrog_inner_symbol_name(expr))
        return extract_hifrog_inner_symbol_L2_counter(expr);
    
    return atoi(to_ssa_expr(expr).get_level_2().c_str());
}

unsigned extract_hifrog_inner_symbol_L2_counter(const exprt &expr){
    std::string test4inned_hifrog = id2string(expr.get(ID_identifier));
    size_t pos = extract_hifrog_inner_symbol_name(expr).size();
    if ((test4inned_hifrog.find(FUNC_RETURN) != std::string::npos) ||
        (test4inned_hifrog.find(TMP_FUNC_RETURN) != std::string::npos) ||
        (test4inned_hifrog.find(CALLSTART_SYMBOL) != std::string::npos) ||
        (test4inned_hifrog.find(CALLEND_SYMBOL) != std::string::npos) ||
        (test4inned_hifrog.find(ERROR_SYMBOL) != std::string::npos))
        return atoi(test4inned_hifrog.substr(pos+1).c_str());
 
    assert(0); // Add constants if needed
}