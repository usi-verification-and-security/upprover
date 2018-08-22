/*******************************************************************\

Module: Wrapper for OpenSMT2

\*******************************************************************/

#ifndef CPROVER_SMTCHECK_OPENSMT2_LRA_H
#define CPROVER_SMTCHECK_OPENSMT2_LRA_H

#include "smtcheck_opensmt2.h"

class smtcheck_opensmt2t_lra : public smtcheck_opensmt2t
{
public:
  smtcheck_opensmt2t_lra(int _type_constraints_level, const char* name) :
          smtcheck_opensmt2t(false, 3, 2),
          type_constraints_level(_type_constraints_level)
  {
    initializeSolver(name);
    ptr_assert_var_constraints = logic->getTerm_true();
  }
      
  virtual ~smtcheck_opensmt2t_lra(); // d'tor

  virtual PTRef expression_to_ptref(const exprt & expr) override;

  virtual literalt const_from_str(const char* num);

  virtual PTRef numeric_constant(const exprt & expr) override;

  virtual PTRef type_cast(const exprt & expr) override;

  // for isnan, mod, arrays etc. that we have no support (or no support yet) create over-approx as nondet
  virtual PTRef unsupported_to_var(const exprt &expr) override;
  
  PTRef abs_to_ptref(const exprt & expr); // from convert for ID_abs

  void check_ce(std::vector<exprt>& exprs); // checking spuriousness of the error trace (not refinement here)
  
  virtual std::string getStringSMTlibDatatype(const typet& type) override;
  virtual SRef getSMTlibDatatype(const typet& type) override;

protected:
  LRALogic* lralogic; // Extra var, inner use only - Helps to avoid dynamic cast!

  PTRef ptr_assert_var_constraints;

  int type_constraints_level; // The level of checks in LRA for numerical checks of overflow

  virtual void initializeSolver(const char*) override;

  PTRef mult_real(const exprt &expr, vec<PTRef> &args);

  PTRef div_real(const exprt &expr, vec<PTRef> &args);

  PTRef runsupported2var(const exprt &expr);

  bool isLinearOp(const exprt &expr, vec<PTRef> &args); // Check if we don't do sth. like nondet*nondet, but only const*nondet (e.g.)
  
  virtual bool can_have_non_linears() override{ return false; }
  
  virtual bool is_non_linear_operator(PTRef tr) override;

  /* Set of functions that add constraints to take care of overflow and underflow */
  void add_constraints2type(const exprt &expr, PTRef& var); // add assume/assert on the data type

  bool push_constraints2type(
  		PTRef &var,
		bool is_non_det,
  		std::string lower_b,
  		std::string upper_b); // Push the constraints of a data type

  void push_assumes2type(
  		PTRef &var,
  		std::string lower_b,
  		std::string upper_b); // Push assume to the higher level

  void push_asserts2type(
  		PTRef &var,
  		std::string lower_b,
  		std::string upper_b); // Push assert to the current partition

  literalt create_constraints2type(
  		PTRef &var,
  		std::string lower_b,
  		std::string upper_b);

  PTRef new_num_var(const std::string & var_name) override;
};

#endif
