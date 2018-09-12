#include "unsupported_operations_opensmt2.h"

#include "../solvers/smtcheck_opensmt2.h"

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
    m_decider->get_function_args(expr, args);
    if (args.size() == 0)
        return std::string(); // It is a simple var!
    /* KE: Check later
    bool is_expr_has_unsupported = m_decider->get_function_args(expr, args);
    if (is_expr_has_unsupported)
        std::cout << "Warning: unsupported operators exist in the original unsupported operator" << std::endl;
    // TODO: check when we have such case!
    */
    
    // Get the function name
    std::string func_id(unsupported_function_name(expr));
    
    // First declare the function, if not exist
    std::string key_func(func_id.c_str());
    key_func += "," + m_decider->to_string_smtlib_datatype(expr.type());
    
    vec<SRef> args_decl;
    for (int i=0; i < args.size(); i++) 
    {
        args_decl.push(m_decider->getLogic()->getSortRef(args[i]));
        key_func += "," + std::string(m_decider->getLogic()->getSortName(m_decider->getLogic()->getSortRef(args[i])));
    }
        
    // Define the function if needed and check it is OK
    if (m_decl_uf.count(key_func) == 0) {
        SymRef decl = SymRef_Undef;
        SRef out = m_decider->get_smtlib_datatype(expr.type());
        decl = add_func_decl2solver(func_id.c_str(), out, args_decl);
        m_decl_uf.insert(std::pair<std::string, SymRef> (key_func,decl));
        assert(decl != SymRef_Undef);
    } 
    
    return key_func; 
}

// Declare new unsupported function as UF
std::string unsupported_operations_opensmt2t::declare_unsupported_function(
                const exprt &expr, const exprt::operandst &operands,
		std::string func_id) 
{
    // Works only if unsupported_operations option is on
    if (!m_can_overapprox)
        return std::string();
    
    // First declare the function, if not exist
    std::string key_func(func_id.c_str());
    
    vec<SRef> args_decl;
    args_decl.push(m_decider->get_smtlib_datatype(expr.type()));
    key_func += "," + m_decider->to_string_smtlib_datatype(expr.type());

    for (auto it : operands) {
      args_decl.push(m_decider->get_smtlib_datatype(it.type()));
      key_func += "," + std::string(m_decider->to_string_smtlib_datatype(it.type()));
    }

    
    // Define the function if needed and check it is OK
    if (m_decl_uf.count(key_func) == 0) {
        SymRef decl = SymRef_Undef;
        SRef out = m_decider->get_smtlib_datatype(expr.type());
        decl = add_func_decl2solver(func_id.c_str(), out, args_decl);
        m_decl_uf.insert(std::pair<std::string, SymRef> (key_func,decl));
        assert(decl != SymRef_Undef);
    } 
    
    return key_func;     
}