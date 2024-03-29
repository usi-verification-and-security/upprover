// Contains all needed functions and constants to translate unsupported 
// operators in the SSA to SMT 

#ifndef UNSUPPORTEDOPERATIONS_H
#define UNSUPPORTEDOPERATIONS_H

#include <string>
#include <vector>
#include <util/expr.h>

struct HifrogStringUnsupportOpConstants {
  static const std::string UNSUPPORTED_VAR_NAME;
  static const std::string UNSUPPORTED_PREFIX_FUNC_NAME;
};

#define unsupported_symbol(x) HifrogStringUnsupportOpConstants::UNSUPPORTED_VAR_NAME + x // To create in general unsupported symbol

// Purpose: create non-linear fresh variable with a separate(independent) counter for summary refinement
std::string fresh_var_name_nonlinear();

// Purpose: extract all unsupported function calls (uns_* e.g.,)
std::vector<std::string> get_unsupported_funct_exprs(std::string const & text);

// Token we ignore and do not model
bool is_in_blacklist(const std::string & fname);

// Check if variable name was created as part of unsupported mechanism
bool is_unsupported_var_name(const std::string & name);

// Create unsupported UF function name
std::string unsupported_function_name(const exprt& expr);

class unsupported_operationst
{
public:
    unsupported_operationst(bool _store_unsupported_info)
            :store_unsupported_info(_store_unsupported_info)
    {}
            
    virtual ~unsupported_operationst() {}
            
    // Create new unsupported L2 Variable
    std::string create_new_unsupported_var(std::string type_name, bool no_rename=false, bool no_quote=false);
    
    // Declare new unsupported function as UF
    virtual std::string declare_unsupported_function(const exprt &expr) =0;
    
    // Declare new unsupported function as UF
    virtual std::string declare_unsupported_function(
                const exprt &expr, const exprt::operandst &operands,
		std::string func_id) =0;
    
    // Info. during error trace creating (in case of failure)
    std::string get_failure_reason(std::string _fails_type_id);
    
    
    
    
    /// TODO: REFACTOR ///
    bool is_store_unsupported_info() { return store_unsupported_info; }
    
    bool has_unsupported_info() const { return store_unsupported_info && has_unsupported_vars(); } // Common to all
    bool has_unsupported_vars() const { return (unsupported2var > 0); } // Common to all, affects several locations!
    void init_unsupported_counter() { unsupported2var=0; } // KE: only for re-init solver use. Once we have pop in OpenSMT, please discard.

    // Shall be in protected - KE - when have time
    std::vector<exprt> unsupported_info_equations; // Keep the whole equation of expressions in unsupported_info_map
    
    // The storage itself
    void store_new_unsupported_var(const exprt& expr, std::string var);
    
    unsigned get_unsupported_info_map_size() { return global_unsupported_str2expr_info.size();}
    std::vector<std::pair<std::string,exprt>>::const_iterator get_itr_unsupported_info_map() const { return global_unsupported_str2expr_info.begin(); }
    std::vector<std::pair<std::string,exprt>>::const_iterator get_itr_end_unsupported_info_map() const { return global_unsupported_str2expr_info.end(); }
    /// TODO: REFACTOR - END ///
    
protected:  
    static unsigned unsupported2var; // Create a new var hifrog::c::unsupported_op2var#i - smtcheck_opensmt2t::_unsupported_var_str
  
    static std::vector<std::pair<std::string,exprt>> global_unsupported_str2expr_info; // String to Expression - can pass between solvers!
      
    bool store_unsupported_info;
  
};

// Add here derived class per solver
// Create a new derived class please

#endif /* UNSUPPORTEDOPERATIONS_H */
