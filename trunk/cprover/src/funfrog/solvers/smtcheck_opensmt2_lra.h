/*******************************************************************\

Module: Wrapper for OpenSMT2

\*******************************************************************/

#ifndef CPROVER_SMTCHECK_OPENSMT2_LRA_H
#define CPROVER_SMTCHECK_OPENSMT2_LRA_H

#include "smtcheck_opensmt2.h"

#include <opensmt/opensmt2.h>
#include <expr.h>

class smtcheck_opensmt2t_lra : public smtcheck_opensmt2t
{
public:
  smtcheck_opensmt2t_lra(int _type_constraints_level) :
      lralogic (NULL),
      type_constraints_level(_type_constraints_level),
      smtcheck_opensmt2t(false, 3, 2)
  {
    initializeSolver();
  }

  virtual ~smtcheck_opensmt2t_lra(); // d'tor

  virtual exprt get_value(const exprt &expr);

  virtual literalt convert(const exprt &expr);

  virtual literalt const_var_Real(const exprt &expr);

  virtual literalt type_cast(const exprt &expr);

  virtual literalt lconst(const exprt &expr);

  // for isnan, mod, arrays etc. that we have no support (or no support yet) create over-approx as nondet
  virtual literalt lunsupported2var(const exprt expr);

  virtual literalt lvar(const exprt &expr);

  virtual literalt lassert_var() { literalt l; l = smtcheck_opensmt2t::push_variable(ptr_assert_var_constraints); return l;}

  LRALogic * getLRALogic() { return lralogic; }

protected:

  LRALogic* lralogic;

  PTRef ptr_assert_var_constraints;

  int type_constraints_level; // The level of checks in LRA for numerical checks of overflow

  void initializeSolver();

  PTRef mult_real(const exprt &expr, vec<PTRef> &args);

  PTRef div_real(const exprt &expr, vec<PTRef> &args);

  PTRef runsupported2var(const exprt expr);

  bool isLinearOp(const exprt &expr, vec<PTRef> &args); // Check if we don't do sth. like nondet*nondet, but only const*nondet (e.g.)

  /* Set of functions that add constraints to take care of overflow and underflow */
  void add_constraints2type(const exprt &expr, PTRef &var); // add assume/assert on the data type

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
  		std::string upper_b); // create a formula with the constraints

  std::string create_bound_string(std::string base, int exp); // build the string of the upper and lower bounds
};

#endif
