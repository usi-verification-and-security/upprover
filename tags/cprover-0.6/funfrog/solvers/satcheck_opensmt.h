/*******************************************************************\

Module: OpenSMT wrapper for propositional logic. Based on
satcheck_minisat.

Author: Ondrej Sery

\*******************************************************************/

#ifndef CPROVER_SATCHECK_OPENSMT_H
#define CPROVER_SATCHECK_OPENSMT_H

#include <vector>

#include <solvers/sat/cnf.h>

#include "interpolating_solver.h"
#define PRODUCE_PROOF
#include "OpenSMTContext.h"

class satcheck_opensmtt:public cnf_solvert, public interpolating_solvert
{
public:
  satcheck_opensmtt(int verbosity = 0, bool _dump_queries = false);
  
  virtual ~satcheck_opensmtt() {
    freeSolver();
  }
  
  virtual resultt prop_solve();
  virtual tvt l_get(literalt a) const;

  virtual void lcnf(const bvt &bv);
  virtual const std::string solver_text();
  virtual void set_assignment(literalt a, bool value);

  // extra MiniSat feature: solve with assumptions
  virtual void set_assumptions(const bvt &_assumptions);

  virtual bool is_in_conflict(literalt a) const;
  virtual bool has_set_assumptions() const { return true; }
  virtual bool has_is_in_conflict() const { return true; }

  // Begins a partition of formula for latter reference during
  // interpolation extraction. All assertions made until
  // next call of new_partition() will be part of this partition.
  //
  // returns a unique partition id
  virtual fle_part_idt new_partition();

  // Extracts the symmetric interpolant of the specified set of
  // partitions. This method can be called only after solving the
  // the formula with an UNSAT result
  virtual void get_interpolant(const interpolation_taskt& partition_ids,
    interpolantst& interpolants, double reduction_timeout) const;

  // Is the solver ready for interpolation? I.e., the solver was used to decide
  // a problem and the result was UNSAT
  virtual bool can_interpolate() const;
  
  const std::string& get_last_var() { return id_str; }
  
protected:
  // Solver verbosity
  unsigned solver_verbosity;
  // Dump all queries?
  bool dump_queries;
  // OpenSMT API entry point
  OpenSMTContext* opensmt_ctx;
  // Shortcut for the bool sort;
  Snode* sbool;
  // List of clauses that are part of this partition
  Enode* partition_root_enode;
  // Count of the created partitions (the last one is open until a call to
  // prop_solve occurs)
  unsigned partition_count;
  // Mapping from variable indices to their E-nodes in OpenSMT
  std::vector<Enode*> enodes;
  // Helper string for mangling the variable names
  std::string id_str;
  // Can we interpolate?
  bool ready_to_interpolate;
  
  // Extract interpolant form OpenSMT Egraph
  void extract_itp(const Enode* enode, prop_itpt& target_itp) const;
  // Cache of already visited interpolant Enodes
  typedef std::map<enodeid_t, literalt> enode_cachet;
  // Simple recursive extraction of clauses from OpenSMT Egraph
  literalt extract_itp_rec(const Enode* enode, prop_itpt& target_itp, 
    enode_cachet& enode_cache) const;
  
  // Initialize the OpenSMT context
  void initializeSolver();
  // Free all resources related to OpenSMT
  void freeSolver();

  void add_variables();
  void increase_id();
  unsigned decode_id(const char* id) const;
  void close_partition();
  Enode* convert(const bvt &bv);
};

#endif
