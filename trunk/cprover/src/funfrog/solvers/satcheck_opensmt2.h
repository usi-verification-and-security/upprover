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
#include "funfrog/interface/solver/interpolating_solver.h"
#include <opensmt/opensmt2.h>

#include <solvers/prop/prop_conv.h>
#include <funfrog/utils/expressions_utils.h>
#include <solvers/flattening/boolbv.h>

class prop_itpt;
class boolbv_mapt;

class satcheck_opensmt2t:public cnf_solvert, public check_opensmt2t
{
public:
  satcheck_opensmt2t(const char* name, const namespacet & ns);

  virtual ~satcheck_opensmt2t() {
    freeSolver();
  }

    bool is_overapprox_encoding() const override;

    bool solve() override {
      auto res = get_bv_converter().dec_solve();
      switch (res){
          case decision_proceduret::resultt::D_SATISFIABLE:
              return true;
          case decision_proceduret::resultt::D_UNSATISFIABLE:
              return false;
          case decision_proceduret::resultt::D_ERROR:
              throw "Error during solving!";
      }
  }

  bool is_overapproximating() const override {return false;}

  virtual resultt prop_solve() override;
  virtual tvt l_get(literalt a) const override;
  bool is_assignment_true(literalt l) const override {
      auto res = l_get(l);
      return res.is_true();
  }

  exprt get_value(const exprt &expr) override {
      return get_bv_converter().get(expr);
  }

  virtual void lcnf(const bvt &bv) override;

    virtual literalt land(literalt l1, literalt l2) override {
        return cnf_solvert::land(l1, l2);
    }
    virtual literalt lor(literalt l1, literalt l2) override {
        return cnf_solvert::lor(l1, l2);
    }

    virtual literalt lor(bvt const & bv) override {
        return cnf_solvert::lor(bv);
    }

    virtual void set_equal(literalt l1, literalt l2) override {
        return cnf_solvert::set_equal(l1, l2);
    }

  const virtual std::string solver_text() override;
  virtual void set_assignment(literalt a, bool value) override;
  // extra MiniSat feature: solve with assumptions
  virtual void set_assumptions(const bvt& _assumptions) override;
  virtual bool is_in_conflict(literalt a) const override;

  virtual bool has_set_assumptions() const override { return true; }

  virtual bool has_is_in_conflict() const override { return true; }

  virtual void insert_substituted(const itpt & itp, const std::vector<symbol_exprt> & symbols) override;

  const boolbvt & get_bv_converter() const {return *boolbv_convert;}
  boolbvt & get_bv_converter() {return *boolbv_convert;}

    void assert_literal(literalt lit) override{
      this->l_set_to_true(lit);
  }



#ifdef PRODUCE_PROOF  
  virtual void get_interpolant(const interpolation_taskt& partition_ids,
      interpolantst& interpolants) const override;
  
  virtual bool can_interpolate() const override;

  // Extract interpolant form OpenSMT Egraph
  void extract_itp(PTRef ptref, prop_itpt& target_itp) const;

  // Simple recursive extraction of clauses from OpenSMT Egraph
  literalt extract_itp_rec(PTRef ptref, prop_itpt& target_itp,
    ptref_cachet& ptref_cache) const;

  void generalize_summary(itpt * interpolant, std::vector<symbol_exprt> & common_symbols) override;

  void generalize_summary(prop_itpt& itp, const std::vector<symbol_exprt>& symbols);
#endif
  
  const std::string& get_last_var() { return id_str; }

protected:
  // Use in the convert from SSA -> SMT-prop encoding

  // Solver verbosity
  unsigned solver_verbosity;
  // Mapping from variable indices to their E-nodes in PeRIPLO
  std::string id_str;

  literalt bool_expr_to_literal(const exprt & expr) override {
      assert(is_boolean(expr));
      return get_bv_converter().convert(expr);
  }

  void set_prop_conv_solvert(std::unique_ptr<boolbvt> converter) {boolbv_convert = std::move(converter);}

#ifdef PRODUCE_PROOF  
  void setup_reduction();

  void setup_interpolation();

  void setup_proof_transformation();

#endif
public:
    literalt new_variable() override;

protected:

    std::vector<std::string> lits_names;

    void set_variable_name(literalt a, const std::string & name) override;

  // Initialize the OpenSMT context
  virtual void initializeSolver(const char*) override;


  void add_variables();
  void increase_id();
  unsigned decode_id(const char* id) const;

private:
    std::unique_ptr<boolbvt> boolbv_convert;
};

#endif
