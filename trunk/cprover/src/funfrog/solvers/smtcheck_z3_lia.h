/*******************************************************************\

Module: Wrapper for Z3

\*******************************************************************/

#ifndef CPROVER_SMTCHECK_Z3_LIA_H
#define CPROVER_SMTCHECK_Z3_LIA_H

#include "smtcheck_z3.h"

class smtcheck_z3_liat : public smtcheck_z3t
{
public:
    // Defualt C'tor, data to init are from smt_params class in Z3, token are in smt_params_helper
    smtcheck_z3_liat(const solver_optionst solver_options) :
            smtcheck_z3t(solver_options, "QF_LIA"),
            m_ptr_assert_var_constraints(nullptr),
            m_type_constraints(solver_options.m_type_constraints)
    { initialize_solver(); }

    virtual ~smtcheck_z3_liat() {} // d'tor
   
    virtual FlaRef get_and_clear_var_constraints() override;
    
    virtual z3::sort get_numeric_sort() override { return m_query_context.int_sort(); }
    
protected:
    
    z3::expr* m_ptr_assert_var_constraints;
    
    unsigned m_type_constraints;
     
    virtual z3::expr evar(const exprt &expr, std::string var_name) override;
    
    virtual z3::expr numeric_constant(const exprt &expr) override;
    
    virtual z3::expr type_cast(const exprt &expr) override;
    
    virtual z3::expr abs_to_ptref(const exprt &expr) override;
        
    void initialize_solver();
    
    virtual void add_symbol_constraints(const exprt &expr, const z3::expr var) override {
        if(m_type_constraints > 0){
            add_constraints2type(expr, var);
        }
    }
    
    virtual void add_to_asset_expr(z3::expr constraint) override
    { m_ptr_assert_var_constraints = new z3::expr(constraint && *m_ptr_assert_var_constraints); }
    
    z3::expr create_constraints2type(
        const z3::expr var,
        std::string lower_b,
        std::string upper_b) override;
    
    unsigned get_type_constraints_level() override { return m_type_constraints;}
};

#endif // CPROVER_SMTCHECK_Z3_LIA_H
