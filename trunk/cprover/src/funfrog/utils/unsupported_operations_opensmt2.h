/* 
 * File:   unsupported_operations_opensmt2.h
 * Author: karinek
 *
 * Created on 31 August 2018, 13:11
 */
#ifndef UNSUPPORTED_OPERATIONS_OPENSMT2_H
#define UNSUPPORTED_OPERATIONS_OPENSMT2_H

#include "unsupported_operations.h"

// Add all solvers basic definition
#include <opensmt/opensmt2.h>

class smtcheck_opensmt2t;

// Any function with SRRef or PTRef
class unsupported_operations_opensmt2t : public unsupported_operationst
{
public:
    unsupported_operations_opensmt2t(bool _store_unsupported_info, smtcheck_opensmt2t* _decider)
            :unsupported_operationst(_store_unsupported_info),
             m_decider(_decider),
             m_can_overapprox(true)
    { m_can_overapprox = (m_decider!=0);}

    virtual ~unsupported_operations_opensmt2t() {}
    
    virtual std::string declare_unsupported_function(const exprt &expr) override; 
    
    // Declare new unsupported function as UF
    virtual std::string declare_unsupported_function(
                const exprt &expr, const exprt::operandst &operands,
		std::string func_id) override;
    
    SymRef get_declaration(std::string decl_str)
    { assert(m_decl_uf.count(decl_str) > 0); return m_decl_uf.at(decl_str); }
    
private:
    // Hold uninterpreted functions that the solver was told about
    std::map<std::string,SymRef> m_decl_uf;
    
    // Decider which we use
    smtcheck_opensmt2t* m_decider;
    
    // Can overapprox expression in the current theory in decider?
    bool m_can_overapprox;
    
    SymRef add_func_decl2solver(const char* op, SRef& in_dt, vec<SRef>& out_dt); // common to all
};

#endif /* UNSUPPORTED_OPERATIONS_OPENSMT2_H */

