/*******************************************************************\

Module: Wrapper for OpenSMT2. Based on satcheck_minisat.

Author: Grigory Fedyukovich

\*******************************************************************/

#ifndef CPROVER_SATCHECK_OPENSMT2_H
#define CPROVER_SATCHECK_OPENSMT2_H

#include <vector>

#include <solvers/sat/cnf.h>
#include <util/threeval.h>
#include "check_opensmt2.h"
#include "interpolating_solver.h"
#include <opensmt/opensmt2.h>

class prop_itpt;
class satcheck_opensmt2t:public cnf_solvert, public check_opensmt2t
{
public:
  satcheck_opensmt2t(const char* name) :
      check_opensmt2t(false, 3, 2) // Is last always!
  {
    initializeSolver(name);
  }

  virtual ~satcheck_opensmt2t() {
    freeSolver();
  }

  virtual resultt prop_solve();
  virtual tvt l_get(literalt a) const;

  virtual void lcnf(const bvt &bv);
  const virtual std::string solver_text();
  virtual void set_assignment(literalt a, bool value);
  // extra MiniSat feature: solve with assumptions
  virtual void set_assumptions(const bvt& _assumptions);
  virtual bool is_in_conflict(literalt a) const;

  virtual bool has_set_assumptions() const { return true; }

  virtual bool has_is_in_conflict() const { return true; }

#ifdef PRODUCE_PROOF  
  virtual void get_interpolant(const interpolation_taskt& partition_ids,
      interpolantst& interpolants);
  
  virtual bool can_interpolate() const;

  // Extract interpolant form OpenSMT Egraph
  void extract_itp(PTRef ptref, prop_itpt& target_itp) const;

  // Simple recursive extraction of clauses from OpenSMT Egraph
  literalt extract_itp_rec(PTRef ptref, prop_itpt& target_itp,
    ptref_cachet& ptref_cache) const;
#endif
  
  const std::string& get_last_var() { return id_str; }

  const char* false_str = "false";
  const char* true_str = "true";

protected:
  // Use in the convert from SSA -> SMT-prop encoding

  // Solver verbosity
  unsigned solver_verbosity;
  // Mapping from variable indices to their E-nodes in PeRIPLO
  std::string id_str;

//  Mapping from variable indices to their PTRefs in OpenSMT
  std::vector<PTRef> ptrefs;
 
  void convert(const bvt &bv, vec<PTRef> &args);

#ifdef PRODUCE_PROOF  
  void setup_reduction();

  void setup_interpolation();

  void setup_proof_transformation();

#endif  
  
  // Initialize the OpenSMT context
  virtual void initializeSolver(const char*);

  // Free all resources related to PeRIPLO
  virtual void freeSolver();

  void add_variables();
  void increase_id();
  unsigned decode_id(const char* id) const;
};

#endif
