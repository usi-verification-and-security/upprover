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
  smtcheck_opensmt2t_lra() :
      lralogic (NULL)
  {
    initializeSolver();
  }

  virtual ~smtcheck_opensmt2t_lra(); // d'tor

  virtual exprt get_value(const exprt &expr);

  virtual literalt convert(const exprt &expr);

  virtual literalt const_var_Real(const exprt &expr);

  virtual literalt type_cast(const exprt &expr);

  PTRef mult_real(const exprt &expr, vec<PTRef> &args);

  PTRef div_real(const exprt &expr, vec<PTRef> &args);

  virtual literalt lconst(const exprt &expr);

  // for isnan, mod, arrays etc. that we have no support (or no support yet) create over-approx as nondet
  PTRef runsupported2var(const exprt expr);
  virtual literalt lunsupported2var(const exprt expr);

  virtual literalt lvar(const exprt &expr);

  LRALogic * getLRALogic() { return lralogic; }

protected:

  LRALogic* lralogic;

  void initializeSolver();

  bool isLinearOp(const exprt &expr, vec<PTRef> &args); // Check if we don't do sth. like nondet*nondet, but only const*nondet (e.g.)

  void add_constraints2type(const exprt &expr, PTRef &var);
  void push_constraints2type(PTRef &var, std::string lower_b, std::string upper_b);
  std::string create_bound_string(std::string base, int exp);
};

#endif
