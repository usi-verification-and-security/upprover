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

  int check_ce(std::vector<exprt>& exprs);

  bool refine_ce(std::vector<exprt>& exprs, int i);

protected:
  CUFLogic* cuflogic; // Extra var, inner use only - Helps to avoid dynamic cast! 

  BVLogic* bvlogic;

  BitBlaster* bitblaster;
    
  virtual literalt lunsupported2var(exprt expr); // for isnan, mod, arrays ect. that we have no support (or no support yet) create over-approx as nondet

  virtual void initializeSolver();

};

#endif
