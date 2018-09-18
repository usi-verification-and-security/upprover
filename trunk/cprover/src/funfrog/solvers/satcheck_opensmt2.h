/*******************************************************************\

Module: Wrapper for OpenSMT2. Based on satcheck_minisat.

Author: Grigory Fedyukovich

\*******************************************************************/

#ifndef CPROVER_SATCHECK_OPENSMT2_H
#define CPROVER_SATCHECK_OPENSMT2_H

#include "check_opensmt2.h"
#include <funfrog/interface/solver/interpolating_solver.h>
#include <funfrog/utils/expressions_utils.h>
#include <opensmt/opensmt2.h>

#include <solvers/sat/cnf.h>
#include <solvers/prop/prop_conv.h>
#include <solvers/flattening/boolbv.h>
#include <util/threeval.h>

#include <vector>
#include <memory>

class prop_itpt;
class boolbv_mapt;

class satcheck_opensmt2t:public cnf_solvert, public check_opensmt2t
{
public:
    satcheck_opensmt2t(const solver_optionst solver_options, const char* name, const namespacet & ns);

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
      throw std::logic_error("Unreachable");
    }

    bool is_overapproximating() const override {return false;}

    virtual resultt prop_solve() override;
    virtual tvt l_get(literalt a) const override;

    bool is_assignment_true(FlaRef l) const override {
        auto res = l_get(flaref_to_literal(l));
        return res.is_true();
    }

    exprt get_value(const exprt &expr) override {
        return get_bv_converter().get(expr);
    }

    using cnf_solvert::land;
    using convertort::land;
    using cnf_solvert::lor;
    using convertort::lor;
    using cnf_solvert::set_equal;
    using convertort::set_equal;

    virtual void lcnf(const bvt &bv) override;

    FlaRef land(FlaRef l1, FlaRef l2) override {
        return literal_to_flaref(cnf_solvert::land(
                flaref_to_literal(l1),
                flaref_to_literal(l2)
        ));
    }
    FlaRef lor(FlaRef l1, FlaRef l2) override {
        return literal_to_flaref(cnf_solvert::lor(
                flaref_to_literal(l1),
                flaref_to_literal(l2)
        ));
    }

    FlaRef lor(std::vector<FlaRef> const & fv) override {
        bvt bv{fv.size()};
        std::transform(fv.begin(), fv.end(), bv.begin(), [](const FlaRef f) { return flaref_to_literal(f);});
        return literal_to_flaref(cnf_solvert::lor(bv));
    }

    void set_equal(FlaRef l1, FlaRef l2) override {
        return cnf_solvert::set_equal(
                flaref_to_literal(l1),
                flaref_to_literal(l2));
    }

    const virtual std::string solver_text() override;
    virtual void set_assignment(literalt a, bool value) override;
    // extra MiniSat feature: solve with assumptions
    virtual void set_assumptions(const bvt& _assumptions) override;
    virtual bool is_in_conflict(literalt a) const override;

    virtual bool has_set_assumptions() const override { return true; }

    virtual bool has_is_in_conflict() const override { return true; }

    void insert_substituted(const itpt & itp, const std::vector<symbol_exprt> & symbols) override;

    const boolbvt & get_bv_converter() const {return *boolbv_convert;}
    boolbvt & get_bv_converter() {return *boolbv_convert;}

    void assert_literal(FlaRef lit) override{
        this->l_set_to_true(flaref_to_literal(lit));
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

    literalt new_variable() override;

protected:
    // Use in the convert from SSA -> SMT-prop encoding

    // Solver verbosity
    unsigned solver_verbosity;
    // Mapping from variable indices to their E-nodes in PeRIPLO
    std::string id_str;

    FlaRef convert_bool_expr(const exprt &expr) override {
        assert(is_boolean(expr));
        return literal_to_flaref(get_bv_converter().convert(expr));
    }
    
    void convert(const vector<literalt> & bv, vec<PTRef> & args);

    void set_prop_conv_solvert(std::unique_ptr<boolbvt> converter) {boolbv_convert = std::move(converter);}

#ifdef PRODUCE_PROOF  
    void setup_reduction();

    void setup_interpolation();

    void setup_proof_transformation();

#endif

    std::vector<std::string> lits_names;

    virtual void set_variable_name(literalt a, const irep_idt & name) override
    { set_variable_name(a, std::string{name.c_str()}); }
    void set_variable_name(literalt a, const std::string & name);

    // Initialize the OpenSMT context
    virtual void initializeSolver(solver_optionst solver_options, const char*) override;


    void add_variables();
    void increase_id();
    unsigned decode_id(const char* id) const;

private:
    std::unique_ptr<boolbvt> boolbv_convert;
};

#endif
