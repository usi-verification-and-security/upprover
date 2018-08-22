/*******************************************************************\

Module: Wrapper for OpenSMT2

\*******************************************************************/

#ifndef CPROVER_SMTCHECK_OPENSMT2_LRA_H
#define CPROVER_SMTCHECK_OPENSMT2_LRA_H

#include "smtcheck_opensmt2_la.h"

class smtcheck_opensmt2t_lra : public smtcheck_opensmt2t_la {
public:
    smtcheck_opensmt2t_lra(unsigned int _type_constraints_level, const char * name) :
            smtcheck_opensmt2t_la(_type_constraints_level, name) {
        initializeSolver(name);
        ptr_assert_var_constraints = logic->getTerm_true();
    }

    virtual ~smtcheck_opensmt2t_lra(); // d'tor

    void check_ce(std::vector<exprt> & exprs); // checking spuriousness of the error trace (not refinement here)

    virtual std::string getStringSMTlibDatatype(const typet & type) override;

    virtual SRef getSMTlibDatatype(const typet & type) override;

protected:
    virtual void initializeSolver(const char *) override;
};

#endif
