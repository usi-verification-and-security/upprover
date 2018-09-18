/*******************************************************************\

Module: Wrapper for OpenSMT2

\*******************************************************************/

#ifndef CPROVER_SMTCHECK_OPENSMT2_H
#define CPROVER_SMTCHECK_OPENSMT2_H

#include "check_opensmt2.h"

#include "../utils/unsupported_operations_opensmt2.h" // KE: shall move all the code of unsupported here
#include <funfrog/utils/expressions_utils.h>
#include <util/symbol.h>
#include <solvers/prop/literal.h>

#include <map>

class smt_itpt;
class symbol_exprt;

// Cache of already visited interpolant literals
typedef std::map<PTRef, literalt> ptref_cachet;

class smtcheck_opensmt2t : public check_opensmt2t
{
public:
    smtcheck_opensmt2t(): check_opensmt2t(), unsupported_info{false, this}
    {}

    virtual ~smtcheck_opensmt2t(); // d'tor

    bool solve() override;

    bool is_overapproximating() const override {return true;}

    bool is_assignment_true(FlaRef fr) const override; // Common to all

    using check_opensmt2t::set_to_true;
    void set_to_true(PTRef); // Common to all

    void set_equal(FlaRef l1, FlaRef l2) override; // Common to all

    virtual FlaRef convert_bool_expr(const exprt & expr) override {
        assert(is_boolean(expr));
        const PTRef ptref = expression_to_ptref(expr);
        // FIXME: PTRef to literal should maybe consider negation, caching...
        return ptref_to_flaref(ptref);
    }

    FlaRef land(FlaRef l1, FlaRef l2) override; // Common to all

    FlaRef lor(FlaRef l1, FlaRef l2) override; // Common to all

    FlaRef lor(const vector<FlaRef> & b) override; // Common to all

    void assert_literal(const FlaRef lit) override{
        set_to_true(flaref_to_ptref(lit));
    }
  
#ifdef PRODUCE_PROOF
    virtual void get_interpolant(const interpolation_taskt& partition_ids,
        interpolantst& interpolants) const override;

    virtual bool can_interpolate() const override;

    // Extract interpolant form OpenSMT files/data
    void extract_itp(PTRef ptref, smt_itpt& target_itp) const; // Common to all

    void generalize_summary(itpt * interpolant, std::vector<symbol_exprt> & common_symbols) override;

    void generalize_summary(smt_itpt & interpolant, std::vector<symbol_exprt> & common_symbols);

    std::set<PTRef> get_non_linears() const;
#endif

    void insert_substituted(const itpt & itp, const std::vector<symbol_exprt> & symbols) override;
  
    // Common to all
  
    std::string getSimpleHeader(); // Get all the declarations without the variables

    exprt get_value(const exprt &expr) override;

    void dump_function(std::ostream& out, const Tterm& templ) {
        logic->dumpFunction(out, templ);
    }

      virtual bool is_overapprox_encoding() const override
      { return (unsupported_info.has_unsupported_vars() && !has_overappox_mapping());}

      virtual SRef get_numeric_sort() const=0; // used in core

      SRef get_smtlib_datatype(const typet & type); // Shall be public

      std::string to_string_smtlib_datatype(const typet & type);

      bool get_function_args(const exprt &expr, vec<PTRef>& args); // common to all
    
protected:
    /****************** Conversion methods - methods for converting expressions to OpenSMT's PTRefs ***************/
    virtual PTRef expression_to_ptref(const exprt& expr) = 0;

    PTRef get_from_cache(const exprt& expr) const;

    void store_to_cache(const exprt& expr, PTRef ptref);

    virtual PTRef symbol_to_ptref(const exprt& expr);

    virtual PTRef new_num_var(const std::string & var_name) = 0;

    virtual PTRef new_bool_var(const std::string& var_name) {
        return logic->mkBoolVar(var_name.c_str());
    }

    std::set<PTRef> get_constants() const;
    
    virtual PTRef constant_to_ptref(const exprt& expr);

    PTRef constant_bool(bool val) const {
        return val ? logic->getTerm_true() : logic->getTerm_false();
    }

    virtual PTRef complex_symbol_to_ptref(const exprt& expr);

    virtual PTRef type_cast(const exprt & expr) = 0;

    virtual PTRef numeric_constant(const exprt &expr) = 0;

    virtual void add_symbol_constraints(const exprt &expr, const PTRef var) {}
    
  /* ***************************************************************************************************************/


    vec<SymRef> function_formulas;

    using expr_hasht = irep_hash;
    //using expr_hasht = irep_full_hash;
    std::unordered_map<exprt, PTRef, expr_hasht> unsupported_expr2ptrefMap;
    std::unordered_map<exprt, PTRef, expr_hasht> expression_to_ptref_map;

    unsupported_operations_opensmt2t unsupported_info;

    bool has_overappox_mapping() const { return unsupported_info.has_unsupported_info(); }

    virtual void init_unsupported_counter() { unsupported_info.init_unsupported_counter(); }
    virtual unsupported_operationst& get_unsupported_info() { return unsupported_info;}

    void store_new_unsupported_var(const exprt& expr, const PTRef var); // common to all

    // virtual literalt lunsupported2var(const exprt &expr)=0; // for isnan, mod, arrays ect. that we have no support (or no support yet) create over-approx as nondet
    virtual PTRef unsupported_to_var(const exprt & expr) = 0;

    PTRef create_unsupported_uf_call(const exprt &expr); // common to all

    FlaRef ptref_to_flaref(PTRef ptl); // Common to all

    PTRef mkFun(SymRef decl, const vec<PTRef>& args); // Common to all

    template<typename Pred, typename Cont_Ret, typename Cont_Cache>
    void collect_rec(const Pred predicate, PTRef ptref, Cont_Ret& collected, Cont_Cache& seen) const {
      if (contains(seen, ptref)) { return; } // already processed
      if (predicate(ptref)) {
          collected.insert(ptref);
      }
      seen.insert(ptref);
      // recurse on children
      auto const & pterm = logic->getPterm(ptref);
      for (auto i = 0; i < pterm.size(); ++i) {
          collect_rec(predicate, pterm[i], collected, seen);
      }
    }

#ifdef PRODUCE_PROOF
    void setup_reduction();

    void setup_interpolation();

    void setup_proof_transformation();

#endif

    virtual bool can_have_non_linears() const {return true;}

    virtual bool is_non_linear_operator(PTRef tr) const = 0;

    // Common to all
    std::string extract_expr_str_name(const exprt &expr); // General method for extracting the name of the var

    irep_idt get_value_from_solver(PTRef ptrf)
    {
      if (logic->hasSortBool(ptrf))
      {
          lbool v1 = mainSolver->getTermValue(ptrf);
          int int_v1 = toInt(v1);
          irep_idt value(std::to_string(int_v1).c_str());

          return value;
      }
      else
      {
          ValPair v1 = mainSolver->getValue(ptrf);
          assert(v1.val != nullptr);
          irep_idt value(v1.val);

          return value;
      }
    }

    bool is_value_from_solver_false(PTRef ptrf)
    {
      assert(logic->hasSortBool(ptrf));

      lbool v1 = mainSolver->getTermValue(ptrf);
      return (toInt(v1) == 0);
    }

#ifdef DISABLE_OPTIMIZATIONS
    std::map <std::string,std::string> ite_map_str;
    typedef std::map<std::string,std::string>::iterator it_ite_map_str;

    std::string getVarData(const PTRef &var) {
            return string(logic->getSortName(logic->getSortRef(var)));
    }
#endif
    // Basic prints for debug - KE: Hope I did it right :-)
    char* getPTermString(const PTRef &term) { return logic->printTerm(term);}

};

#endif
