/*******************************************************************\

Module: Wrapper for Z3

\*******************************************************************/

#ifndef CPROVER_SMTCHECK_Z3_EUF_H
#define CPROVER_SMTCHECK_Z3_EUF_H

#include "smtcheck_z3.h"

class smtcheck_z3_uft : public smtcheck_z3t
{
public:
    // Defualt C'tor, data to init are from smt_params class in Z3, token are in smt_params_helper
    smtcheck_z3_uft(const solver_optionst solver_options) :
            smtcheck_z3t(solver_options, "QF_UF")
    { initialize_solver(); }

    virtual ~smtcheck_z3_uft() {} // d'tor
   
    virtual z3::sort get_numeric_sort() override { return *sort_unumber; }
  
protected:

    void initialize_solver();
    
    virtual z3::expr evar(const exprt &expr, std::string var_name) override;
    
    virtual z3::expr convert(const exprt &expr) override;
        
    virtual z3::expr numeric_constant(const exprt &expr) override;
    
    virtual z3::expr type_cast(const exprt &expr) override;
    
    virtual void add_to_asset_expr(z3::expr constraint) override { assert(0); }
    
    z3::expr create_constraints2type(const z3::expr var,std::string lower_b,std::string upper_b) override {assert(0);}
    
    unsigned get_type_constraints_level() override { return 0;}
    
private:
        
    static const char *tk_sort_unumber;
    static const char *tk_mult;
    static const char *tk_div;
    static const char *tk_plus;
    static const char *tk_minus;
    static const char *tk_lt;
    static const char *tk_le;
    static const char *tk_gt;
    static const char *tk_ge;
    static const char *tk_neg;  
    
    z3::sort* sort_unumber;
    
    z3::func_decl s_mult ();
    z3::func_decl s_div  ();  
    z3::func_decl s_plus ();  
    z3::func_decl s_minus(); 
    z3::func_decl s_lt   ();
    z3::func_decl s_le   ();
    z3::func_decl s_gt   ();
    z3::func_decl s_ge   ();
    z3::func_decl s_neg  ();
    z3::func_decl s_pos  ();
};

#endif // CPROVER_SMTCHECK_Z3_EUF_H
