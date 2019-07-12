/*******************************************************************\

Module: Wrapper for OpenSMT2

\*******************************************************************/

#ifndef CPROVER_SMTCHECK_OPENSMT2_LRA_H
#define CPROVER_SMTCHECK_OPENSMT2_LRA_H

#include "smtcheck_opensmt2_la.h"

class smtcheck_opensmt2t_lra : public smtcheck_opensmt2t_la {
public:
    smtcheck_opensmt2t_lra(const solver_optionst solver_options, const char * name) :
            smtcheck_opensmt2t_la(solver_options.m_type_constraints, name) {   // calls base class constructor
        initializeSolver(solver_options,name);
        ptr_assert_var_constraints = logic->getTerm_true();
    }

    virtual ~smtcheck_opensmt2t_lra(); // d'tor

    void check_ce(std::vector<exprt> & exprs); // checking spuriousness of the error trace (not refinement here)

protected:
    virtual void initializeSolver(const solver_optionst solver_options, const char *) override;
    
    virtual PTRef numeric_constant(const exprt & expr) override;
    
#ifdef PRODUCE_PROOF
    
    void set_lra_factor(std::string factor) {itp_lra_factor = std::move(factor);}

#endif //PRODUCE_PROOF
};

#endif
