/*******************************************************************\

Module: Wrapper for OpenSMT2. Based on satcheck_minisat.

Author: Grigory Fedyukovich

\*******************************************************************/
#include "smtcheck_opensmt2_lia.h"
#include <util/type.h>

/*******************************************************************\

Function: smtcheck_opensmt2t_lia::initializeSolver

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
void smtcheck_opensmt2t_lia::initializeSolver(const char* name)
{
    osmt = new Opensmt(opensmt_logic::qf_lia, name);
    lalogic = &(osmt->getLIALogic());
    logic = &(osmt->getLIALogic());
    mainSolver = &(osmt->getMainSolver());

#ifndef NDEBUG
    // To avoid issues with type constraints for LIA
    if (type_constraints_level > 0)
        std::cout << "Adding Type Constraints (" << type_constraints_level << ")" 
                << ((type_constraints_level == 1 ? " for type constraints on non-deterministic input" : ""))
                << ((type_constraints_level == 2 ? " for type constraints on variables" : ""))
                << ((type_constraints_level >= 3  ? " ** ERROR ** Unknown Option" : ""))
                << std::endl;
#endif // NDEBUG not defined
}

/*******************************************************************\

Function: smtcheck_opensmt2t_lia::~smtcheck_opensmt2t_lia

  Inputs:

 Outputs:

 Purpose: Free all inner objects

\*******************************************************************/
smtcheck_opensmt2t_lia::~smtcheck_opensmt2t_lia()
{
    // Shall/When need to: freeSolver() ?
}

/*******************************************************************\

Function: smtcheck_opensmt2t_lia::getStringSMTlibDatatype

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
std::string smtcheck_opensmt2t_lia::getStringSMTlibDatatype(const typet& type)
{ 
    if ((type.id()==ID_bool) || (type.id() == ID_c_bool))
        return SMTConstants::SMT_BOOL;
    if (is_number(type))
        return SMTConstants::SMT_INT;
    
    return SMTConstants::SMT_UNKNOWN; // Shall not get here
}

/*******************************************************************\

Function: smtcheck_opensmt2t_lia::getSMTlibDatatype

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
SRef smtcheck_opensmt2t_lia::getSMTlibDatatype(const typet& type)
{ 
    if ((type.id()==ID_bool) || (type.id() == ID_c_bool))
        return lalogic->getSort_bool(); //SMT_BOOL
    if (is_number(type))
        return lalogic->getSort_num(); // SMT_INT

    throw std::logic_error("Unknown datatype encountered!");
}
