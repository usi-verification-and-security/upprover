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
void smtcheck_opensmt2t_lia::initializeSolver(solver_optionst solver_options, const char* name)
{
    osmt = new Opensmt(opensmt_logic::qf_lia, name);
    lalogic = &(osmt->getLIALogic());
    logic = &(osmt->getLIALogic());
    mainSolver = &(osmt->getMainSolver());

    // Initialize parameters
    this->verbosity = solver_options.m_verbosity;
    set_random_seed(solver_options.m_random_seed);
  
#ifdef PRODUCE_PROOF  
    // TODO: add sets once interpolation is working for LIA
#endif
#ifdef DISABLE_OPTIMIZATIONS
    set_dump_query(solver_options.m_dump_query);
    dump_pre_queries = solver_options.m_dump_pre_query;
    set_dump_query_name(solver_options.m_dump_query_name);
#endif // DISABLE_OPTIMIZATIONS  
    
#ifndef NDEBUG
    // To avoid issues with type constraints for LIA
    ptr_assert_var_constraints = logic->getTerm_true();
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