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

  virtual literalt convert(const exprt &expr);

  virtual literalt const_var_Real(const exprt &expr);

  virtual literalt type_cast(const exprt &expr);

  virtual literalt lconst(const exprt &expr);

  virtual literalt lunsupported2var(exprt expr); // for isnan, mod, arrays etc. that we have no support (or no support yet) create over-approx as nondet
  	  	  	  	  	  	  	  	  	  	 // Remove when has a support for UF

  virtual literalt lvar(const exprt &expr);
  
  virtual std::string extract_expr_str_name(const exprt &expr); // General method for extracting the name of the var

  LRALogic * getLRALogic() { return lralogic; }

protected:

  LRALogic* lralogic;

  void initializeSolver();

  bool isLinearOp(const exprt &expr, vec<PTRef> &args); // Check if we don't do sth. like nondet*nondet, but only const*nondet (e.g.)

};

#endif
