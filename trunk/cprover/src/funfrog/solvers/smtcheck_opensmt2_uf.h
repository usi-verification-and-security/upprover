/*******************************************************************\

Module: Wrapper for OpenSMT2

\*******************************************************************/

#ifndef CPROVER_SMTCHECK_OPENSMT2_UF_H
#define CPROVER_SMTCHECK_OPENSMT2_UF_H

#include <map>
#include <vector>

#include <util/threeval.h>
#include "smtcheck_opensmt2.h"
#include "interpolating_solver.h"
#include "smt_itp.h"
#include <opensmt/opensmt2.h>
#include <expr.h>
#include "smtcheck_opensmt2.h"

// Cache of already visited interpolant literals
typedef std::map<PTRef, literalt> ptref_cachet;

class smtcheck_opensmt2t_uf : public smtcheck_opensmt2t
{
public:
  smtcheck_opensmt2t_uf(const char* name) :
      smtcheck_opensmt2t(false, 3, 2) // Is last always!
  {
    initializeSolver(name);
  }

  virtual ~smtcheck_opensmt2t_uf(); // d'tor
  
  virtual exprt get_value(const exprt &expr);

  virtual literalt convert(const exprt &expr);

  virtual literalt const_var_Real(const exprt &expr);
  
  virtual literalt type_cast(const exprt &expr);

  virtual literalt lnotequal(literalt l1, literalt l2);

  virtual literalt lvar(const exprt &expr);

protected:

  virtual literalt lunsupported2var(exprt expr); // for isnan, mod, arrays ect. that we have no support (or no support yet) create over-approx as nondet

  virtual void initializeSolver(const char* name);
  
  static const char *tk_sort_ureal;
  static const char *tk_mult;
  static const char *tk_div;
  static const char *tk_plus;
  static const char *tk_minus;
  static const char *tk_lt;
  static const char *tk_le;
  static const char *tk_gt;
  static const char *tk_ge;

  SRef sort_ureal; //Uninterpreted Real sort. Used to fake LRA.
  SymRef s_mult, s_div, s_plus, s_minus;
  SymRef s_lt, s_le, s_gt, s_ge;

  // Only for UF
  PTRef mkURealMult(vec<PTRef>& args);
  PTRef mkURealDiv(vec<PTRef>& args);
  PTRef mkURealPlus(vec<PTRef>& args);
  PTRef mkURealMinus(vec<PTRef>& args);
  PTRef mkURealLt(vec<PTRef>& args);
  PTRef mkURealLe(vec<PTRef>& args);
  PTRef mkURealGt(vec<PTRef>& args);
  PTRef mkURealGe(vec<PTRef>& args);

};

#endif
