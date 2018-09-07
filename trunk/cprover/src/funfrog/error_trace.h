#ifndef ERROR_TRACE_H_
#define ERROR_TRACE_H_

#include <util/expr.h>
#include <goto-programs/goto_trace.h>
#include <funfrog/interface/solver/solver.h>
#include "partitioning_target_equation.h"

class hifrog_symex_target_equationt;
class partitioning_target_equationt;
class solvert;

class error_tracet {
public:
	// Status of over-approx checking and results
	enum flagOverApproxt { UNKNOWN, REAL, SPURIOUS };
	typedef enum flagOverApproxt isOverAppoxt;

	// C'tor
	error_tracet() :
		isOverAppox(error_tracet::isOverAppoxt::UNKNOWN) {}

	// D'tor
	virtual ~error_tracet() {}

	void build_goto_trace(
			const SSA_steps_orderingt &SSA_steps,
			solvert &solver);
        
	void show_goto_trace(
	  std::ostream &out,
	  const namespacet &ns,
	  std::map<irep_idt, std::string> &guard_expln); // MAIN: from prepare_smt_formula

     error_tracet::isOverAppoxt is_trace_overapprox(solvert &solver, const SSA_steps_orderingt &SSA_steps);


        ////////////////////////////////////////////
// Theoref lra experimental version; for now it is commented out
/*	void build_goto_trace_formula (
	  partitioning_target_equationt &target,
	  smtcheck_opensmt2t &decider,
	  smtcheck_opensmt2t_lra &decider2); */

	void build_goto_trace_formula(
            std::vector<exprt> &exprs,
            std::map<const exprt, int> &model,
            solvert &solver);


private:
	isOverAppoxt isOverAppox;
	goto_tracet goto_trace; // The error trace

	void show_state_header(
			  std::ostream &out,
			  const unsigned thread_nr,
			  const source_locationt &location,
			  unsigned step_nr);

	void show_guard_value(
	  std::ostream &out,
	  const std::string &str,
	  const exprt &value);

	void show_misc_value(
	  std::ostream &out,
	  const irep_idt &str,
	  const exprt &value);

	void show_var_value(
	  std::ostream &out,
	  const namespacet &ns,
	  const symbol_exprt &lhs_object,
	  const exprt &full_lhs,
	  const exprt &value);

	void show_expr(
	  std::ostream &out,
	  const namespacet &ns,
	  const irep_idt &identifier,
	  const exprt &expr,
	  bool is_removed);

	bool is_index_member_symbol(const exprt &src);
};

#endif /* ERROR_TRACE_H_ */
