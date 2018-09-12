#ifndef UNSUPPORTED_OPERATIONS_Z3_H
#define UNSUPPORTED_OPERATIONS_Z3_H

#include "unsupported_operations.h"
#include <vector>

// Add all solvers basic definition
#include <z3++.h>
#include <z3_api.h>
using namespace z3;

class smtcheck_z3t;

// Any function with SRRef or PTRef
class unsupported_operations_z3t : public unsupported_operationst
{
public:
    unsupported_operations_z3t(bool _store_unsupported_info, smtcheck_z3t* _decider)
            :unsupported_operationst(_store_unsupported_info),
             m_decider(_decider),
             m_can_overapprox(true)
    { m_can_overapprox = (m_decider!=0);}
    
    virtual ~unsupported_operations_z3t() {}
    
    virtual std::string declare_unsupported_function(const exprt &expr) override; 
    
    // Declare new unsupported function as UF
    virtual std::string declare_unsupported_function(
                const exprt &expr, const exprt::operandst &operands,
		std::string func_id) override;
    
    z3::func_decl get_declaration(std::string decl_str)
    { assert(m_decl_uf.count(decl_str) > 0); return m_decl_uf.at(decl_str); }
    
private:
    // Hold uninterpreted functions that the solver was told about
    std::map<std::string,z3::func_decl> m_decl_uf;
    
    // Decider which we use
    smtcheck_z3t* m_decider;
    
    // Can overapprox expression in the current theory in decider?
    bool m_can_overapprox;
    
    z3::func_decl add_func_decl2solver(const char* op, const z3::sort& in_dt, std::vector<z3::sort>& out_dt); // common to all
};

#endif /* UNSUPPORTED_OPERATIONS_Z3_H */

