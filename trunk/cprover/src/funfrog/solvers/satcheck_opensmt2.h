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
#include "prop_itp.h"
#include <opensmt/opensmt2.h>

// Cache of already visited interpolant ptrefs
typedef std::map<PTRef, literalt> ptref_cachet;

class satcheck_opensmt2t:public cnf_solvert, public interpolating_solvert, public check_opensmt2t
{
public:
  satcheck_opensmt2t() :
      itp_algorithm(2),
      check_opensmt2t(false, 3, 2) // Is last always!
  {
    initializeSolver();
  }

  virtual ~satcheck_opensmt2t() {
    freeSolver();
  }

  virtual prop_conv_solvert* get_prop_conv_solver() {return prop_conv_interface;}
  void set_prop_conv_solver(prop_conv_solvert* _prop) { prop_conv_interface = _prop;}

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

  // Begins a partition of formula for latter reference during
  // interpolation extraction. All assertions made until
  // next call of new_partition() will be part of this partition.
  //
  // returns a unique partition id
  virtual fle_part_idt new_partition();

  virtual void get_interpolant(const interpolation_taskt& partition_ids,
      interpolantst& interpolants);

  virtual bool can_interpolate() const;

  // Extract interpolant form OpenSMT Egraph
  void extract_itp(PTRef ptref, prop_itpt& target_itp) const;

  // Simple recursive extraction of clauses from OpenSMT Egraph
  literalt extract_itp_rec(PTRef ptref, prop_itpt& target_itp,
    ptref_cachet& ptref_cache) const;
 
  const std::string& get_last_var() { return id_str; }

  const char* false_str = "false";
  const char* true_str = "true";

protected:
  // Use in the convert from SSA -> SMT-prop encoding
  prop_conv_solvert* prop_conv_interface;

  // Solver verbosity
  unsigned solver_verbosity;
  // Mapping from variable indices to their E-nodes in PeRIPLO
  std::string id_str;
  // Can we interpolate?
  bool ready_to_interpolate;
  
  vec<PTRef> top_level_formulas;

  int reduction_loops;

  int reduction_graph;

  // 0 - McMillan, 1 - Pudlak, 2 - McMillan'
  int itp_algorithm;
  //SMTConfig::ItpAlgorithm itp_algorithm;

  // 1 - stronger, 2 - weaker (GF: not working at the moment)
  int proof_trans;

//  Mapping from variable indices to their PTRefs in OpenSMT
  std::vector<PTRef> ptrefs;

  void convert(const bvt &bv, vec<PTRef> &args);

  void setup_reduction();

  void setup_interpolation();

  void setup_proof_transformation();
  
  // Initialize the OpenSMT context
  virtual void initializeSolver();

  // Free all resources related to PeRIPLO
  virtual void freeSolver();
  void produceConfigMatrixInterpolants (const vector< vector<int> > &configs, vector<PTRef> &interpolants);

  void add_variables();
  void increase_id();
  unsigned decode_id(const char* id) const;
  void close_partition();
};

#endif
