// Contains all needed functions and constants to translate unsupported 
// operators in the SSA to SMT 

#ifndef UNSUPPORTEDOPERATIONS_H
#define UNSUPPORTEDOPERATIONS_H

#include <opensmt/opensmt2.h>

#include <string>
#include <vector>
#include <util/expr.h>

class smtcheck_opensmt2t;

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
bool is_in_blacklist(std::string fname);

// Check if variable name was created as part of unsupported mechanism
bool is_unsupported_var_name(std::string name);

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
    std::string create_new_unsupported_var(std::string type_name, bool no_rename=false);
    
    // Declare new unsupported function as UF
    virtual std::string declare_unsupported_function(const exprt &expr) =0;
    
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

// Any function with SRRef or PTRef
class unsupported_operations_opensmt2t : public unsupported_operationst
{
public:
    unsupported_operations_opensmt2t(bool _store_unsupported_info, smtcheck_opensmt2t* _decider)
            :unsupported_operationst(_store_unsupported_info),
             m_decider(_decider),
             m_can_overapprox(_decider == nullptr)
    {}
    
    virtual ~unsupported_operations_opensmt2t() {}
    
    virtual std::string declare_unsupported_function(const exprt &expr) override; 
    
    std::pair<SymRef,vec<PTRef> &> get_declaration(std::string decl_str)
    { assert(m_decl_uf.count(decl_str) > 0); return m_decl_uf.at(decl_str); }
    
private:
    // Hold uninterpreted functions that the solver was told about
    std::map<std::string,std::pair<SymRef,vec<PTRef>& >> m_decl_uf;
    
    // Decider which we use
    smtcheck_opensmt2t* m_decider;
    
    // Can overapprox expression in the current theory in decider?
    bool m_can_overapprox;
    
    SymRef add_func_decl2solver(const char* op, SRef& in_dt, vec<SRef>& out_dt); // common to all
};

// Add here derived class per solver

#endif /* UNSUPPORTEDOPERATIONS_H */
