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

#define PRODUCE_PROOF
#include "OpenSMTContext.h"

class satcheck_opensmtt:public cnf_solvert
{
public:
  satcheck_opensmtt() : partition_root_enode(NULL)
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
  
protected:
  OpenSMTContext* opensmt_ctx;
  Snode* sbool;
  Enode* partition_root_enode;
  vector<Enode*> enodes;
  std::string id_str;

  void add_variables();
  void increase_id();
  Enode* convert(const bvt &bv);
};

#endif
