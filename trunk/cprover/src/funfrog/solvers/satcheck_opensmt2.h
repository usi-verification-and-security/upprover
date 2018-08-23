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
#include "../utils/unsupported_operations.h"

class prop_itpt;
class satcheck_opensmt2t:public cnf_solvert, public check_opensmt2t
{
public:
  satcheck_opensmt2t(const char* _name
#ifdef PRODUCE_PROOF   
    , int _itp_algorithm
    , bool _reduction, unsigned int _reduction_graph, unsigned int _reduction_loops  
#endif
#ifdef DISABLE_OPTIMIZATIONS          
    , bool _dump_queries, bool _dump_pre_queries, std::string _dump_query_name
#endif  
  ) : 
    check_opensmt2t(
#ifdef PRODUCE_PROOF  
        _reduction, _reduction_graph, _reduction_loops   
#else
        false, 3, 2
#endif // Is last always!
#ifdef DISABLE_OPTIMIZATIONS
        , _dump_queries, _dump_pre_queries, _dump_query_name
#endif
    )
  {
    initializeSolver(_name);
    
    // Init of Interpolation - TODO: move into initializeSolver    
#ifdef PRODUCE_PROOF
    itp_algorithm.x = _itp_algorithm;
#endif
  }

  virtual ~satcheck_opensmt2t() {
    freeSolver();
  }

  resultt prop_solve() override;
  virtual bool solve() { return prop_solve() == resultt::P_SATISFIABLE; } // To create single solver interface
  tvt l_get(literalt a) const override;

  void lcnf(const bvt &bv) override;
  const virtual std::string solver_text() override;
  void set_assignment(literalt a, bool value) override;
  // extra MiniSat feature: solve with assumptions
  void set_assumptions(const bvt& _assumptions) override;
  bool is_in_conflict(literalt a) const override;

  bool has_set_assumptions() const override { return true; }

  bool has_is_in_conflict() const override { return true; }

#ifdef PRODUCE_PROOF  
  void get_interpolant(const interpolation_taskt& partition_ids,
      interpolantst& interpolants) override;
  
  bool can_interpolate() const override;

  // Extract interpolant form OpenSMT Egraph
  void extract_itp(PTRef ptref, prop_itpt& target_itp) const;

  // Simple recursive extraction of clauses from OpenSMT Egraph
  literalt extract_itp_rec(PTRef ptref, prop_itpt& target_itp,
    ptref_cachet& ptref_cache) const;
#endif
  
  const std::string& get_last_var() { return id_str; }

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
  void initializeSolver(const char*) override;

  // Free all resources related to PeRIPLO
  void freeSolver() override;

  void add_variables();
  void increase_id();
  unsigned decode_id(const char* id) const;

    // No over-approximation for propositional logic!
    virtual bool has_overappox_mapping() const override { return false; }
    virtual bool has_unsupported_vars() const override { return false; }
};

#endif
