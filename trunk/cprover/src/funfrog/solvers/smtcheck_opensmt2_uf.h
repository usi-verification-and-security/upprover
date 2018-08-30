/*******************************************************************\

Module: Wrapper for OpenSMT2

\*******************************************************************/

#ifndef CPROVER_SMTCHECK_OPENSMT2_UF_H
#define CPROVER_SMTCHECK_OPENSMT2_UF_H

#include "smtcheck_opensmt2.h"

class smtcheck_opensmt2t_uf : public smtcheck_opensmt2t
{
public:
  smtcheck_opensmt2t_uf(const solver_optionst solver_options, const char* name) :
      smtcheck_opensmt2t()
  {
    initializeSolver(solver_options, name);
  }

  virtual ~smtcheck_opensmt2t_uf(); // d'tor

  virtual PTRef expression_to_ptref(const exprt & expr) override;

  virtual PTRef numeric_constant(const exprt &expr) override;
  
  virtual PTRef type_cast(const exprt & expr) override;
  
  virtual SRef get_numeric_sort() const override {return sort_ureal;}
  
protected:

  PTRef new_num_var(const std::string & var_name) override;
    
  virtual PTRef unsupported_to_var(const exprt &expr) override; // for isnan, mod, arrays ect. that we have no support (or no support yet) create over-approx as nondet

  virtual void initializeSolver(const solver_optionst solver_options, const char* name) override;
  
  virtual bool is_non_linear_operator(PTRef tr) const override;
  
private:  

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
