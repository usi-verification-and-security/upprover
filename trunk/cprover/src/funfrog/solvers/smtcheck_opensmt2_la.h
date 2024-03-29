/*******************************************************************\

Module: Wrapper for OpenSMT2

\*******************************************************************/

#ifndef CPROVER_SMTCHECK_OPENSMT2_LA_H
#define CPROVER_SMTCHECK_OPENSMT2_LA_H

#include "smtcheck_opensmt2.h"

class smtcheck_opensmt2t_la : public smtcheck_opensmt2t
{
public:
    smtcheck_opensmt2t_la(unsigned int _type_constraints_level, const char* name) :
            smtcheck_opensmt2t(),
            type_constraints_level(_type_constraints_level)
    {
        lalogic = new LRALogic();
        logic.reset(lalogic);
    }
      
    virtual ~smtcheck_opensmt2t_la(); // d'tor
    
    virtual FlaRef get_and_clear_var_constraints() override;
    
    virtual PTRef expression_to_ptref(const exprt & expr) override;
    
    virtual SRef get_numeric_sort() const override {return lalogic->getSort_num();}
    
protected:
    LALogic* lalogic; // Extra var, inner use only - Helps to avoid dynamic cast!

    // TODO: investigate if constraints should not be handled differently
    PTRef ptr_assert_var_constraints;

    unsigned int type_constraints_level; // The level of checks in LA for numerical checks of overflow

    virtual PTRef type_cast(const exprt & expr) override;

    PTRef new_num_var(const std::string & var_name) override;

    PTRef mult_numbers(const exprt &expr, vec<PTRef> &args);

    PTRef div_numbers(const exprt &expr, vec<PTRef> &args);

    PTRef abs_to_ptref(const exprt & expr);
    // for isnan, mod, arrays etc. that we have no support (or no support yet) create over-approx as nondet
    virtual PTRef unsupported_to_var(const exprt &expr) override;

    bool isLinearOp(const exprt &expr, vec<PTRef> &args); // Check if we don't do sth. like nondet*nondet, but only const*nondet (e.g.)

    virtual bool can_have_non_linears() const override { return false; }

    virtual bool is_non_linear_operator(PTRef tr) const override;
  
    virtual void add_symbol_constraints(const exprt &expr, const PTRef var) override {
        if(type_constraints_level > 0){
            add_constraints2type(expr, var);
        }
    }
      
    /* Set of functions that add constraints to take care of overflow and underflow */
    void add_constraints2type(const exprt & expr, const PTRef var); // add assume/assert on the data type

    bool push_constraints2type(
            const PTRef var,
            bool is_non_det,
            std::string lower_b,
            std::string upper_b); // Push the constraints of a data type

    void push_assumes2type(
            const PTRef var,
            std::string lower_b,
            std::string upper_b); // Push assume to the higher level

    void push_asserts2type(
            const PTRef var,
            std::string lower_b,
            std::string upper_b); // Push assert to the current partition

    PTRef create_constraints2type(
            const PTRef var,
            std::string lower_b,
            std::string upper_b); // create a formula with the constraints

};

#endif
