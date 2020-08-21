/*******************************************************************\

Module: Wrapper for OpenSMT2

\*******************************************************************/

#ifndef CPROVER_SMTCHECK_OPENSMT2_LIA_H
#define CPROVER_SMTCHECK_OPENSMT2_LIA_H

#include "smtcheck_opensmt2_la.h"

class smtcheck_opensmt2t_lia : public smtcheck_opensmt2t_la {
public:
    smtcheck_opensmt2t_lia(const solver_optionst solver_options, const char * name) :
            smtcheck_opensmt2t_la(solver_options.m_type_constraints, name)
    {
        lalogic = new LIALogic();
        logic.reset(lalogic);
        initializeSolver(solver_options, name);
        ptr_assert_var_constraints = logic->getTerm_true();
    }

    virtual ~smtcheck_opensmt2t_lia(); // d'tor
    
#ifdef PRODUCE_PROOF

    virtual bool can_interpolate() const override { return false; }

#endif
protected:

    virtual void initializeSolver(const solver_optionst solver_options, const char *) override;
    
    virtual PTRef numeric_constant(const exprt & expr) override;

};

#endif
