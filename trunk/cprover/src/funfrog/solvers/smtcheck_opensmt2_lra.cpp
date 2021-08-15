/*******************************************************************\

Module: Wrapper for OpenSMT2. Based on satcheck_minisat.

\*******************************************************************/
#include "smtcheck_opensmt2_lra.h"
#include <util/type.h>
#include <funfrog/utils/naming_helpers.h>

/*******************************************************************\

Function: smtcheck_opensmt2t_lra::initializeSolver

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
void smtcheck_opensmt2t_lra::initializeSolver(solver_optionst solver_options, const char* name)
{
    const char* msg2 = nullptr;
    config->setOption(SMTConfig::o_produce_inter, SMTOption(true), msg2);
    assert(strcmp(msg2, "ok") == 0);
    config->setSimplifyInterpolant(solver_options.simplify_interpolant);
    mainSolver.reset(new MainSolver(*logic, *config, name));
    // Initialize parameters
    this->verbosity = solver_options.m_verbosity;
    set_random_seed(solver_options.m_random_seed);
  
#ifdef PRODUCE_PROOF  
    this->itp_lra_algorithm.x = solver_options.m_lra_itp_algorithm;
    this->set_lra_factor(solver_options.m_lra_factor);

    this->certify = solver_options.m_certify;
    this->reduction = solver_options.m_do_reduce;
    this->reduction_loops = solver_options.m_reduction_loops;
    this->reduction_graph = solver_options.m_reduction_graph;
#endif
#ifdef DISABLE_OPTIMIZATIONS
    set_dump_query(solver_options.m_dump_query);
    dump_pre_queries = solver_options.m_dump_pre_query;
    set_dump_query_name(solver_options.m_dump_query_name);
#endif // DISABLE_OPTIMIZATIONS  
    
#ifndef NDEBUG
    // To avoid issues with type constraints for LRA
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

Function: smtcheck_opensmt2t_lra::~smtcheck_opensmt2t_lra

  Inputs:

 Outputs:

 Purpose: Free all inner objects

\*******************************************************************/
smtcheck_opensmt2t_lra::~smtcheck_opensmt2t_lra()
{
    // Shall/When need to: freeSolver() ?
}

/*******************************************************************\

Function: smtcheck_opensmt2t_lra::numeric_constante

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
PTRef smtcheck_opensmt2t_lra::numeric_constant(const exprt & expr)
{
    std::string num = extract_expr_str_number(expr);
    PTRef rconst = lalogic->mkConst(num.c_str()); // Can have a wrong conversion sometimes!
    assert(rconst != PTRef_Undef);
    
    return rconst;
}

/*******************************************************************\
Function: smtcheck_opensmt2t_lra::check_ce

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
void smtcheck_opensmt2t_lra::check_ce(std::vector<exprt>& exprs)
{
	// this method is used for testing mostly
	char *msg = nullptr;

	for (int i = 0; i < top_level_formulas.size(); i++){
	    char *s = logic->printTerm(top_level_formulas[i]);
		std::cout << "\nCE:  " << s << '\n';
        free(s);
		mainSolver->insertFormula(top_level_formulas[i], &msg);
		if (msg !=nullptr) { free(msg); msg = nullptr; }
	}
	mainSolver->push();

	bool res = true;
	unsigned int i = 0;
	while (i < exprs.size() && res){
	    PTRef lp = expression_to_ptref(exprs[i]);
	    mainSolver->insertFormula(lp, &msg);
	    if (msg != nullptr) { free(msg); msg = nullptr; }
	    res = (s_True == mainSolver->check());
	    if (!res){
                char *s = logic->printTerm(lp);
	    	std::cout << "\n  Problem could be here: " << s << '\n';
                free(s);
	    }
//	    mainSolver->pop();  // TODO: uncomment this line and comment "&& res" in the guard
	    					// to get a segmfalut in the incremental solver
	    i++;
    }
}
