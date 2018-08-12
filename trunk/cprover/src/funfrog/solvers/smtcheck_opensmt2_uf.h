/*******************************************************************\

Module: Wrapper for OpenSMT2

\*******************************************************************/

#ifndef CPROVER_SMTCHECK_OPENSMT2_UF_H
#define CPROVER_SMTCHECK_OPENSMT2_UF_H

#include "smtcheck_opensmt2.h"

class smtcheck_opensmt2t_uf : public smtcheck_opensmt2t
{
public:
  smtcheck_opensmt2t_uf(const char* name) :
      smtcheck_opensmt2t(false, 3, 2) // Is last always!
  {
    initializeSolver(name);
  }

  virtual ~smtcheck_opensmt2t_uf(); // d'tor

  virtual PTRef expression_to_ptref(const exprt & expr) override;

  virtual PTRef numeric_constant(const exprt &expr) override;
  
  virtual PTRef type_cast(const exprt & expr) override;

protected:
    PTRef new_num_var(const std::string & var_name) override;

public:

  virtual literalt lassert_var() override { throw std::logic_error("Looks like this should not be called for this solver"); }
     
  virtual std::string getStringSMTlibDatatype(const typet& type) override;
  virtual SRef getSMTlibDatatype(const typet& type) override;

  SRef getURealSortRef() const {return sort_ureal;}

protected:

  virtual PTRef unsupported_to_var(const exprt &expr) override; // for isnan, mod, arrays ect. that we have no support (or no support yet) create over-approx as nondet

  virtual void initializeSolver(const char* name) override;
  
  virtual bool can_have_non_linears() override { return true; }
  
  virtual bool is_non_linear_operator(PTRef tr) override;
  
  static const char *tk_sort_ureal;
  static const char *tk_mult;
  static const char *tk_div;
  static const char *tk_plus;
  static const char *tk_minus;
  static const char *tk_lt;
  static const char *tk_le;
  static const char *tk_gt;
  static const char *tk_ge;
  static const char *tk_neg;

  SRef sort_ureal; //Uninterpreted Real sort. Used to fake LRA.
  SymRef s_mult, s_div, s_plus, s_minus;
  SymRef s_lt, s_le, s_gt, s_ge;
  SymRef s_neg;

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
