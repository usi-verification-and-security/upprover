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
  smtcheck_opensmt2t_cuf() :
      smtcheck_opensmt2t(false, 3, 2) // Is last always!
  {
    initializeSolver();
  }

  virtual ~smtcheck_opensmt2t_cuf(); // d'tor

  virtual exprt get_value(const exprt &expr);

  virtual literalt convert(const exprt &expr);

  virtual literalt const_var_Real(const exprt &expr);

  virtual literalt type_cast(const exprt &expr);

  virtual literalt lnotequal(literalt l1, literalt l2);

  virtual literalt lvar(const exprt &expr);

  PTRef get_bv_var(const char* name);

  PTRef get_bv_const(int val);

  void set_equal_bv(PTRef l1, PTRef l2);

  PTRef convert_bv(const exprt &expr);

  bool convert_bv_eq_ite(const exprt &expr, PTRef& ptl);

  int check_ce(std::vector<exprt>& exprs);

  bool refine_ce_solo(std::vector<exprt>& exprs, int i); // refine only exprs[i]

  bool refine_ce_mul(std::vector<exprt>& exprs, std::vector<int>& is); // refine only subset of expr

  bool force_refine_ce(std::vector<exprt>& exprs, std::set<int>& refined); // refine all from exprs, but already refined

  PTRef split_exprs(irep_idt id, vec<PTRef>& args);
  PTRef split_exprs_bv(irep_idt id, vec<PTRef>& args);
  
protected:
  BVLogic* bvlogic; // Extra var, inner use only - Helps to avoid dynamic cast!
  CUFLogic* uflogic; // Extra var, inner use only - Helps to avoid dynamic cast!

  BitBlaster* bitblaster;

  map<size_t, PTRef> converted_bitblasted_exprs;
  
  void bindBB(const exprt& expr, PTRef pt1, PTRef pt2);

  void refine_ce_one_iter(std::vector<exprt>& exprs, int i);

  virtual literalt lunsupported2var(exprt expr); // for isnan, mod, arrays ect. that we have no support (or no support yet) create over-approx as nondet

  virtual void initializeSolver();

};

#endif
