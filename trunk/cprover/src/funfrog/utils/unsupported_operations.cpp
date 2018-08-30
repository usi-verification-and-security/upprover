#include "unsupported_operations.h"

#include <assert.h>

#include "../utils/naming_helpers.h"
#include "../solvers/smtcheck_opensmt2.h"

// General/Global Data
const std::string HifrogStringUnsupportOpConstants::UNSUPPORTED_VAR_NAME {"hifrog::c::unsupported_op2var"};
const std::string HifrogStringUnsupportOpConstants::UNSUPPORTED_PREFIX_FUNC_NAME {"uns_"};

unsigned unsupported_operationst::unsupported2var = 0; // Count how many instance of unsupported we have for all deciders
std::vector<std::pair<std::string,exprt>> unsupported_operationst::global_unsupported_str2expr_info;

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
    global_unsupported_str2expr_info.push_back(std::pair<std::string, exprt> (var, expr)); // PTRef sometimes turn into 0
}


/*******************************************************************\

Function: unsupported_operations_opensmt2t::add_func_decl2solver

 Inputs: name of the function and its signature

 Outputs: the function declarations

 Purpose: to create new custom function to smt from summaries

\*******************************************************************/
SymRef unsupported_operations_opensmt2t::add_func_decl2solver(const char* op, SRef& in_dt, vec<SRef>& out_dt) {
    char *msg=nullptr;
    SymRef ret = m_decider->getLogic()->declareFun(op, in_dt, out_dt, &msg, true);
    if (msg != nullptr) free(msg);

    return ret;    
}

/*******************************************************************\

Function: unsupported_operations_opensmt2t::declare_unsupported_function

  Inputs:

 Outputs: the unsupported operator symbol to be used later in
 * mkFun method

 Purpose:
 *  If not exist yet, creates a new declaration in OpenSMT with 
 *  function name+size of args+type. 
\*******************************************************************/
std::string unsupported_operations_opensmt2t::declare_unsupported_function(const exprt &expr)
{
    // Works only if unsupported_operations option is on
    if (!m_can_overapprox)
        return std::string();
    
    // extract parameters to the call
    vec<PTRef> args;
    bool is_expr_has_unsupported = m_decider->get_function_args(expr, args);
    if (is_expr_has_unsupported)
        std::cout << "Warning: unsupported operators exist in the original unsupported operator" << std::endl;
    // TODO: check when we have such case!
    
    // Get the function name
    std::string func_id(unsupported_function_name(expr));
    
    // First declare the function, if not exist
    std::string key_func(func_id.c_str());
    key_func += "," + m_decider->to_string_smtlib_datatype(expr.type());
    SRef out = m_decider->get_smtlib_datatype(expr.type());
    
    vec<SRef> args_decl;
    for (int i=0; i < args.size(); i++) 
    {
        args_decl.push(m_decider->getLogic()->getSortRef(args[i]));
        key_func += "," + std::string(m_decider->getLogic()->getSortName(m_decider->getLogic()->getSortRef(args[i])));
    }
    
    // Define the function if needed and check it is OK
    if (m_decl_uf.count(key_func) == 0) {
        SymRef decl = SymRef_Undef;
        decl = add_func_decl2solver(func_id.c_str(), out, args_decl);
        std::pair<SymRef,vec<PTRef>&> data(std::pair<SymRef,vec<PTRef>&>(decl,args));
        m_decl_uf.insert(std::pair<std::string, std::pair<SymRef,vec<PTRef>&>> (key_func,data));
        assert(decl != SymRef_Undef);
    } 
    
    return key_func; 
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