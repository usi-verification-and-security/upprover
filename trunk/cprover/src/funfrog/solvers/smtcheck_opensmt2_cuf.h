/*******************************************************************\

Module: Wrapper for OpenSMT2

\*******************************************************************/

#ifndef CPROVER_SMTCHECK_OPENSMT2_CUF_H
#define CPROVER_SMTCHECK_OPENSMT2_CUF_H

#include "smtcheck_opensmt2.h"
#include <util/mp_arith.h>

class BitBlaster;

class smtcheck_opensmt2t_cuf : public smtcheck_opensmt2t
{
public:
  smtcheck_opensmt2t_cuf(unsigned bitwidth, int _type_constraints_level, const char* name) :
        smtcheck_opensmt2t(false, 3, 2), // Is last always!
        bitwidth(bitwidth),
        type_constraints_level(_type_constraints_level)
  {
    initializeSolver(name);
  }

  virtual ~smtcheck_opensmt2t_cuf(); // d'tor

  virtual exprt get_value(const exprt &expr) override;

  virtual PTRef expression_to_ptref(const exprt & expr) override;

  virtual PTRef numeric_constant(const exprt & expr) override;

  virtual PTRef new_num_var(const std::string & var_name) override;

  virtual PTRef type_cast(const exprt & expr) override;

  virtual literalt lassert_var() override { throw std::logic_error("Looks like this should not be called for this solver"); }
  
  PTRef var_bv(const exprt &expr); // lvar for bv logic
  
  PTRef get_bv_var(const char* name);

  PTRef get_bv_const(const char* val);

  PTRef convert_bv(const exprt &expr);

  bool convert_bv_eq_ite(const exprt &expr, PTRef& ptl);
  
  PTRef type_cast_bv(const exprt &expr);
  
  PTRef labs_bv(const exprt &expr); // from convert for ID_abs

  int check_ce(std::vector<exprt>& exprs, std::map<const exprt, int>& model,
               std::set<int>& refined, std::set<int>& weak, int start, int end, int step, int do_dep);

  bool refine_ce_solo(std::vector<exprt>& exprs, int i); // refine only exprs[i]

  bool refine_ce_mul(std::vector<exprt>& exprs, std::set<int>& is); // refine only subset of expr

  bool force_refine_ce(std::vector<exprt>& exprs, std::set<int>& refined); // refine all from exprs, but already refined

  PTRef split_exprs(irep_idt id, vec<PTRef>& args);
  PTRef split_exprs_bv(irep_idt id, vec<PTRef>& args);

  std::string get_refinement_failure_reason() {
      if (unsupported2var == 0) {
          return ""; // No unsupported functions, no reason
      }
      
      return "Cannot refine due to " + std::to_string(unsupported2var) + 
              " unsupported operators;e.g., " + id2string(_fails_type_id);
  }
  
  virtual std::string getStringSMTlibDatatype(const typet& type) override;
  virtual SRef getSMTlibDatatype(const typet& type) override;

protected:
  BVLogic* bvlogic; // Extra var, inner use only - Helps to avoid dynamic cast!
  CUFLogic* uflogic; // Extra var, inner use only - Helps to avoid dynamic cast!

  BitBlaster* bitblaster;

  unsigned bitwidth;
  
  int type_constraints_level; // The level of checks in BV logic for numerical checks possible values

  mp_integer max_num; // w.r.t. current bitwidth

  std::map<size_t, PTRef> converted_bitblasted_exprs;

  irep_idt _fails_type_id; // Reason 2 fail of CUF theoref
        
  void bindBB(const exprt& expr, PTRef pt1);

  void refine_ce_one_iter(std::vector<exprt>& exprs, int i);

  virtual PTRef unsupported_to_var(const exprt & expr) override; // for isnan, mod, arrays ect. that we have no support (or no support yet) create over-approx as nondet
  
  PTRef unsupported2var_bv(const exprt &expr); // for BVs
  
  PTRef lconst_bv(const exprt &expr); // For bv only!
  
  virtual void initializeSolver(const char*) override;
  
  void add_constraints4chars_bv(const exprt &expr, PTRef &var);
  
  void add_constraints4chars_bv_char(PTRef &var, const irep_idt type_id_c, const irep_idt type_id);

  void add_constraints4chars_bv_bool(const exprt &expr, PTRef &var, int size, const irep_idt type_id);
  
  void add_constraints4chars_numeric(PTRef &var, int size, const irep_idt type_id);
  
  virtual bool can_have_non_linears() override { return true; } ;
  
  virtual bool is_non_linear_operator(PTRef tr) override;
};

void getVarsInExpr(exprt& e, std::set<exprt>& vars);

// Taken from cprover framework: integer2unsigned, mp_arith.cpp
inline int mp_integer2int(const mp_integer &n)
{
  mp_integer::llong_t ll=n.to_long();
  assert("Framework currently does not support numbers larger than ints" && ll <= std::numeric_limits<int>::max());
  assert("Framework currently does not support numbers smaller than ints" && ll >= std::numeric_limits<int>::min());
  return (int)ll;
}
#endif
