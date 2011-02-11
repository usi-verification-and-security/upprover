/*******************************************************************\

Module: OpenSMT wrapper for propositional logic. Based on
satcheck_minisat.

Author: Ondrej Sery

\*******************************************************************/

#ifndef CPROVER_SATCHECK_OPENSMT_H
#define CPROVER_SATCHECK_OPENSMT_H

#include <vector>
#include <set>

#include <solvers/sat/cnf.h>

#include "interpolating_solver.h"
#define PRODUCE_PROOF
#include "OpenSMTContext.h"

class satcheck_opensmtt:public cnf_solvert, public interpolating_solvert
{
public:
  satcheck_opensmtt() : partition_root_enode(NULL), partition_count(0)
  {
    opensmt_ctx = new OpenSMTContext();
    opensmt_ctx->SetLogic("QF_BOOL");

    SMTConfig& config = opensmt_ctx->getConfig();
    config.setProduceModels();
    // config.setProduceProofs();
    // config.setProduceInter();

    sbool = opensmt_ctx->mkSortBool();
  }
  
  virtual ~satcheck_opensmtt() {
    delete opensmt_ctx;
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
  virtual exprt get_interpolant(const fle_part_idst& partition_ids) const;
  
protected:
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
  vector<Enode*> enodes;
  // Helper string for mangling the variable names
  std::string id_str;

  void add_variables();
  void increase_id();
  void close_partition();
  Enode* convert(const bvt &bv);
};

#endif
