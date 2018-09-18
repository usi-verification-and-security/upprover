#include "unsupported_operations_z3.h"

#include "../solvers/smtcheck_z3.h"
#include <iostream>

/*******************************************************************\

Function: unsupported_operations_z3t::add_func_decl2solver

 Inputs: name of the function and its signature

 Outputs: the function declarations

 Purpose: to create new custom function to smt from summaries

\*******************************************************************/
//unc_decl function(char const * name, sort const & d1, sort const & d2, sort const & d3, sort const & range)
z3::func_decl unsupported_operations_z3t::add_func_decl2solver(const char* op, const z3::sort& in_dt, std::vector<z3::sort>& out_dt) {
    if (out_dt.size() == 1) return z3::function(op, in_dt, out_dt[0]);
    if (out_dt.size() == 2) return z3::function(op, in_dt, out_dt[0], out_dt[1]);
    if (out_dt.size() == 3) return z3::function(op, in_dt, out_dt[0], out_dt[1], out_dt[2]);
    if (out_dt.size() == 4) return z3::function(op, in_dt, out_dt[0], out_dt[1], out_dt[2], out_dt[3]);
    if (out_dt.size() == 5) return z3::function(op, in_dt, out_dt[0], out_dt[1], out_dt[2], out_dt[3], out_dt[4]);
    
    std::cerr << ";; No support for " << out_dt.size() << " operators " << std::endl;
    assert(0); // TODO
}

/*******************************************************************\

Function: unsupported_operations_z3t::declare_unsupported_function

  Inputs:

 Outputs: the unsupported operator symbol to be used later in
 * mkFun method

 Purpose:
 *  If not exist yet, creates a new declaration in OpenSMT with 
 *  function name+size of args+type. 
\*******************************************************************/
std::string unsupported_operations_z3t::declare_unsupported_function(const exprt &expr)
{
    // Works only if unsupported_operations option is on
    if (!m_can_overapprox)
        return std::string();
    
    // extract parameters to the call
    std::vector<z3::expr> args;
    m_decider->get_function_args(expr, args);
    if (args.size() == 0)
        return std::string(); // It is a simple var!
    
    // Get the function name
    std::string func_id(unsupported_function_name(expr));
    
    // First declare the function, if not exist
    std::string key_func(func_id.c_str());
    key_func += "," + m_decider->to_string_smtlib_datatype(expr.type());
    
    std::vector<z3::sort> args_decl;
    for (unsigned i=0; i < args.size(); i++) 
    {
        args_decl.push_back(args[i].get_sort());
        key_func += "," + std::string(args[i].get_sort().to_string());
    }
            
    // Define the function if needed and check it is OK
    if (m_decl_uf.count(key_func) == 0) {
        z3::func_decl decl = add_func_decl2solver(func_id.c_str(), m_decider->get_smtlib_datatype(expr.type()), args_decl);
        m_decl_uf.insert(std::pair<std::string, z3::func_decl> (key_func,decl));
    } 
    
    return key_func; 
}

// Declare new unsupported function as UF
std::string unsupported_operations_z3t::declare_unsupported_function(
                const exprt &expr, const exprt::operandst &operands,
		std::string func_id) 
{
    // Works only if unsupported_operations option is on
    if (!m_can_overapprox)
        return std::string();
    
    // First declare the function, if not exist
    std::string key_func(func_id.c_str());
    
    std::vector<z3::sort> args_decl;
    args_decl.push_back(m_decider->get_smtlib_datatype(expr.type()));
    key_func += "," + m_decider->to_string_smtlib_datatype(expr.type());

    for (auto it : operands) {
      args_decl.push_back(m_decider->get_smtlib_datatype(it.type()));
      key_func += "," + std::string(m_decider->to_string_smtlib_datatype(it.type()));
    }

    
    // Define the function if needed and check it is OK
    if (m_decl_uf.count(key_func) == 0) {
        z3::func_decl decl = add_func_decl2solver(func_id.c_str(), m_decider->get_smtlib_datatype(expr.type()), args_decl);
        m_decl_uf.insert(std::pair<std::string, z3::func_decl> (key_func,decl));
    } 
    
    return key_func;     
}