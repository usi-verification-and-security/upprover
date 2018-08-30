#include "unsupported_operations.h"
#include "../utils/naming_helpers.h"
#include "../solvers/smtcheck_opensmt2.h"
#include <assert.h>

// General/Global Data
const std::string HifrogStringUnsupportOpConstants::UNSUPPORTED_VAR_NAME {"hifrog::c::unsupported_op2var"};
const std::string HifrogStringUnsupportOpConstants::UNSUPPORTED_PREFIX_FUNC_NAME {"uns_"};
unsigned unsupported_operationst::unsupported2var = 0; // Count how many instance of unsupported we have for all deciders
std::vector<std::pair<std::string,exprt>> unsupported_operationst::unsupported_info_items;

/*******************************************************************\

Function: UnsupportedOperationst::create_new_unsupported_var

 Inputs: 

 Outputs: New unsupported global SSA name

 Purpose:

 FIXME: shall fabricate properly the name as SSA expression
 fabricate with l2, and return the name with l2

\*******************************************************************/
std::string unsupported_operationst::create_new_unsupported_var(std::string type_name, bool no_rename)
{
    // Create a new unsupported va
    std::string str = unsupported_symbol(type_name);
    assert(str.size() > 0); 
    return quote_if_necessary(no_rename ? str : (str+"!0#"+ std::to_string(unsupported2var++)));
}

// String for reason to fail in refinement
std::string unsupported_operationst::get_failure_reason(std::string _fails_type_id)
{
    return (!has_unsupported_vars()) ? "" // No unsupported functions, no reason
            : "Cannot refine due to " + std::to_string(unsupported2var) + 
                " unsupported operators;e.g., " + _fails_type_id;
}

/*******************************************************************\
 * 
Function: UnsupportedOperationst::store_new_unsupported_var

 Inputs: 

 Outputs: 

 Purpose: Keep which expressions are not supported and abstracted from 
 * the smt encoding

\*******************************************************************/
void unsupported_operationst::store_new_unsupported_var(const exprt& expr, std::string var) {        
    const irep_idt &_id=expr.id(); // KE: gets the id once for performance
    if (!store_unsupported_info) return;
    if (is_in_blacklist(_id.c_str())) return;
    if ((_id==ID_symbol) || (_id==ID_nondet_symbol) || (_id==ID_constant)) return;
    
    // Add the abstracted expression
    unsupported_info_items.push_back(std::pair<std::string, exprt> (var, expr)); // PTRef sometimes turn into 0
}

// Skip these functions and never try to refine these
bool is_in_blacklist(std::string fname)
{
    static std::set<std::string> black_list_func = {"nil","","exit","thread","nondet"};
    return  (black_list_func.count(fname) > 0);
}

// Check if variable name was created as part of unsupported mechanism
bool is_unsupported_var_name(std::string name)
{
    return (name.find(HifrogStringUnsupportOpConstants::UNSUPPORTED_VAR_NAME) 
            != std::string::npos);
}

// Create unsupported function name
std::string unsupported_function_name(const exprt& expr)
{
    const irep_idt &_func_id=expr.id(); // Which function we will add as uninterpurted
    std::string func_id(_func_id.c_str());
    func_id = HifrogStringUnsupportOpConstants::UNSUPPORTED_PREFIX_FUNC_NAME + func_id;
    return func_id;
}
    
/*******************************************************************/
// SUMMARY REFINEMENT 
// Purpose: create non-linear fresh variable with a separate(independent) counter for summary refinement
// No need to store this information. Once needed shall use the class functionality!
std::string fresh_var_name_nonlinear(){
    static int counter = 0;
    return quote_if_necessary( unsupported_symbol(std::string{"_sumtheoref_"}) + std::to_string(counter++) );
}

// SUMMARY REFINEMENT
// Purpose: extract all unsupported function calls (uns_* e.g.,)
std::vector<std::string> get_unsupported_funct_exprs(std::string const & text) {
    std::vector<std::string> res;
    const std::string UNS = "(uns_";
    std::string::size_type last_pos = 0;
    while ((last_pos = text.find(UNS, last_pos)) != std::string::npos) {
        auto beg = last_pos;
        auto current = beg + 1;
        int counter = 0;
        while (text[current] != ')' || counter > 0) {
            if (text[current] == ')') { --counter; }
            if (text[current] == '(') { ++counter; }
            ++current;
        }
        auto end = current + 1;
        res.push_back(text.substr(beg, end - beg));
//                std::cout << res.back() << '\n';
        last_pos = end;
    }
    return res;
}
