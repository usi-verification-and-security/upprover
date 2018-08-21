/*******************************************************************\

Module: Wrapper for OpenSMT2

\*******************************************************************/

#ifndef CPROVER_SMTCHECK_OPENSMT2_CUF_H
#define CPROVER_SMTCHECK_OPENSMT2_CUF_H

#include "smtcheck_opensmt2.h"
#include <util/mp_arith.h>
#include "../hifrog.h"

class BitBlaster;

class smtcheck_opensmt2t_cuf : public smtcheck_opensmt2t
{
public:
  smtcheck_opensmt2t_cuf(unsigned bitwidth, int _type_constraints_level, const char* name
#ifdef DISABLE_OPTIMIZATIONS          
        , bool _dump_queries, bool _dump_pre_queries, std::string _dump_query_name
#endif
  ) :
        smtcheck_opensmt2t(false, 3, 2
#ifdef DISABLE_OPTIMIZATIONS
        , _dump_queries, _dump_pre_queries, _dump_query_name 
#endif         
        ), // Is last always! // TODO: pass parameters once itp works for CUF
        bitwidth(bitwidth),
        type_constraints_level(_type_constraints_level)      
  {
    initializeSolver(name);
  }

  virtual ~smtcheck_opensmt2t_cuf(); // d'tor

  virtual exprt get_value(const exprt &expr) override;

  virtual literalt convert(const exprt &expr) override;
  
  virtual std::string getStringSMTlibDatatype(const typet& type) override;
  virtual SRef getSMTlibDatatype(const typet& type) override;

  int check_ce(std::vector<exprt>& exprs, std::map<const exprt, int>& model,
               std::set<int>& refined, std::set<int>& weak, int start, int end, int step, int do_dep);

  bool refine_ce_solo(std::vector<exprt>& exprs, int i); // refine only exprs[i]

  bool refine_ce_mul(std::vector<exprt>& exprs, std::set<int>& is); // refine only subset of expr

  bool force_refine_ce(std::vector<exprt>& exprs, std::set<int>& refined); // refine all from exprs, but already refined

  std::string get_refinement_failure_reason() { return unsupported_info.get_failure_reason(id2string(_fails_type_id)); } 
  
protected:
  BVLogic* bvlogic; // Extra var, inner use only - Helps to avoid dynamic cast!
  CUFLogic* uflogic; // Extra var, inner use only - Helps to avoid dynamic cast!

  BitBlaster* bitblaster;

  unsigned bitwidth;
  
  int type_constraints_level; // The level of checks in BV logic for numerical checks possible values

  mp_integer max_num; // w.r.t. current bitwidth

  std::map<size_t, PTRef> converted_bitblasted_exprs;

  irep_idt _fails_type_id; // Reason 2 fail of CUF theoref
          
  virtual void initializeSolver(const char*) override;  
  
  virtual literalt lunsupported2var(const exprt &expr) override; // for isnan, mod, arrays ect. that we have no support (or no support yet) create over-approx as nondet

  void add_constraints4chars_bv(const exprt &expr, PTRef &var);
  
  void add_constraints4chars_bv_char(PTRef &var, const irep_idt type_id_c, const irep_idt type_id);

  void add_constraints4chars_bv_bool(const exprt &expr, PTRef &var, int size, const irep_idt type_id);
  
  void add_constraints4chars_numeric(PTRef &var, int size, const irep_idt type_id);
  
  virtual PTRef make_var(const std::string name) override
  { return uflogic->mkCUFNumVar(name.c_str()); }

  virtual bool can_have_non_linears() override { return true; } ;
  
  virtual bool is_non_linear_operator(PTRef tr) override;
  
  virtual literalt lconst_number(const exprt &expr) override;

  virtual literalt ltype_cast(const exprt &expr) override;
 
  virtual PTRef evar(const exprt &expr, std::string var_name) override;
  
  PTRef split_exprs(irep_idt id, vec<PTRef>& args);
  PTRef split_exprs_bv(irep_idt id, vec<PTRef>& args);
  
  void refine_ce_one_iter(std::vector<exprt>& exprs, int i);

  void bindBB(const exprt& expr, PTRef ptl);

  PTRef unsupported2var_bv(const exprt &expr); // for BVs
  
  PTRef lconst_bv(const exprt &expr); // For bv only!
  
  PTRef var_bv(const exprt &expr); // lvar for bv logic
  
  PTRef get_bv_var(const char* name);

  PTRef get_bv_const(const char* val);

  PTRef convert_bv(const exprt &expr);

  bool convert_bv_eq_ite(const exprt &expr, PTRef& ptl);
  
  PTRef type_cast_bv(const exprt &expr);
  
  PTRef labs_bv(const exprt &expr); // from convert for ID_abs
};

#endif
