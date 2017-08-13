/*******************************************************************\

Module: Wrapper for OpenSMT2

\*******************************************************************/

#ifndef CPROVER_SMTCHECK_OPENSMT2_CUF_H
#define CPROVER_SMTCHECK_OPENSMT2_CUF_H

#include <map>
#include <vector>

#include <util/threeval.h>
#include "smtcheck_opensmt2.h"
#include "interpolating_solver.h"
#include "smt_itp.h"
#include <opensmt/opensmt2.h>
#include <opensmt/BitBlaster.h>
#include <expr.h>

// Cache of already visited interpolant literals
typedef std::map<PTRef, literalt> ptref_cachet;

class smtcheck_opensmt2t_cuf : public smtcheck_opensmt2t
{
public:
  smtcheck_opensmt2t_cuf(unsigned bitwidth, int _type_constraints_level, const char* name) :
      type_constraints_level(_type_constraints_level),
      bitwidth(bitwidth),        
      smtcheck_opensmt2t(false, 3, 2) // Is last always!
  {
    initializeSolver(name);
  }

  virtual ~smtcheck_opensmt2t_cuf(); // d'tor

  virtual exprt get_value(const exprt &expr);

  virtual literalt convert(const exprt &expr);

  virtual literalt const_var_Real(const exprt &expr);

  virtual literalt type_cast(const exprt &expr);

  virtual literalt lnotequal(literalt l1, literalt l2);

  virtual literalt lvar(const exprt &expr);
  
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
  
  virtual std::string getStringSMTlibDatatype(const exprt& expr);
  virtual SRef getSMTlibDatatype(const exprt& expr);

protected:
  BVLogic* bvlogic; // Extra var, inner use only - Helps to avoid dynamic cast!
  CUFLogic* uflogic; // Extra var, inner use only - Helps to avoid dynamic cast!

  BitBlaster* bitblaster;

  unsigned bitwidth;
  
  int type_constraints_level; // The level of checks in BV logic for numerical checks possible values

  mp_integer max_num; // w.r.t. current bitwidth

  map<size_t, PTRef> converted_bitblasted_exprs;

  irep_idt _fails_type_id; // Reason 2 fail of CUF theoref
        
  void bindBB(const exprt& expr, PTRef pt1);

  void refine_ce_one_iter(std::vector<exprt>& exprs, int i);

  virtual literalt lunsupported2var(const exprt &expr); // for isnan, mod, arrays ect. that we have no support (or no support yet) create over-approx as nondet
  
  PTRef unsupported2var_bv(const exprt &expr); // for BVs
  
  PTRef lconst_bv(const exprt &expr); // For bv only!
  
  virtual void initializeSolver(const char*);
  
  void add_constraints4chars_bv(const exprt &expr, PTRef &var);
  
  void add_constraints4chars_bv_char(PTRef &var, const irep_idt type_id_c, const irep_idt type_id);

  void add_constraints4chars_bv_bool(const exprt &expr, PTRef &var, int size, const irep_idt type_id);
  
  void add_constraints4chars_numeric(PTRef &var, int size, const irep_idt type_id);
};

inline void getVarsInExpr(exprt& e, std::set<exprt>& vars)
{
  if(e.id()==ID_symbol){
    if (smtcheck_opensmt2t::is_cprover_builtins_var(e)) 
    { 
        // Skip rounding_mode or any other builtins vars
    } 
    else
    {
        vars.insert(e);
    }
  } else if (e.has_operands()){
    for (unsigned int i = 0; i < e.operands().size(); i++){
      getVarsInExpr(e.operands()[i], vars);
    }
  }
}

// Taken from cprover framework: integer2unsigned, mp_arith.cpp
inline int mp_integer2int(const mp_integer &n)
{
  mp_integer::llong_t ll=n.to_long();
  assert("Framework currently does not support numbers larger than ints" && ll <= std::numeric_limits<int>::max());
  assert("Framework currently does not support numbers smaller than ints" && ll >= std::numeric_limits<int>::min());
  return (int)ll;
}
#endif
