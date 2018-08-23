/*******************************************************************\

Module: Wrapper for OpenSMT2

\*******************************************************************/

#ifndef CPROVER_SMTCHECK_OPENSMT2_H
#define CPROVER_SMTCHECK_OPENSMT2_H

#include <map>
#include <vector>

#include "check_opensmt2.h"
#include <funfrog/utils/expressions_utils.h>
#include <util/expr.h>
#include <util/symbol.h>
#include <solvers/prop/literal.h>

class smt_itpt;
class symbol_exprt;

// Cache of already visited interpolant literals
typedef std::map<PTRef, literalt> ptref_cachet;

// FIXME: add inheritance for class messaget, and replace couts in status/warning/error
// This shall be to all smt interface classes
class smtcheck_opensmt2t : public check_opensmt2t
{
public:
  // Defualt C'tor
  smtcheck_opensmt2t() :
    smtcheck_opensmt2t(false, 3, 2)
  {
    /* No init of solver - done for inherit check_opensmt2 */
  }

  // C'tor to pass the value to main interface check_opensmt2
  smtcheck_opensmt2t(bool reduction, int reduction_graph, int reduction_loops) :
        check_opensmt2t(reduction, reduction_graph, reduction_loops)
  { /* No init of solver - done for inherit check_opensmt2 */}

  virtual ~smtcheck_opensmt2t(); // d'tor

  bool solve() override;

  bool is_overapproximating() const override {return true;}

  bool is_assignment_true(literalt a) const override; // Common to all

  using check_opensmt2t::set_to_true;
  void set_to_true(PTRef); // Common to all

  void set_equal(literalt l1, literalt l2) override; // Common to all

  virtual literalt bool_expr_to_literal(const exprt & expr) override{
      assert(is_boolean(expr));
      const PTRef ptref = expression_to_ptref(expr);
      // FIXME: PTRef to literal should maybe consider negation, caching...
      return push_variable(ptref);
  }

  literalt land(literalt l1, literalt l2) override; // Common to all

  literalt land(bvt b); // Common to all

  literalt lor(literalt l1, literalt l2) override; // Common to all

  literalt lor(const bvt & b) override; // Common to all

  virtual void lcnf(const bvt& bv) override;

  void assert_literal(literalt lit) override{
      set_to_true(literalToPTRef(lit));
  }

#ifdef PRODUCE_PROOF
  virtual void get_interpolant(const interpolation_taskt& partition_ids,
      interpolantst& interpolants) const override;

  virtual bool can_interpolate() const override;

  // Extract interpolant form OpenSMT files/data
  virtual void extract_itp(PTRef ptref, smt_itpt& target_itp) const; // Common to all

  void generalize_summary(itpt * interpolant, std::vector<symbol_exprt> & common_symbols) override;

  void generalize_summary(smt_itpt & interpolant, std::vector<symbol_exprt> & common_symbols);

  set<PTRef> get_non_linears(); // Common to all, needed only if there are summaries!
#endif

  /* The data: lhs, original function data */
  bool has_unsupported_vars() const { return (unsupported2var > 0); } // Common to all, affects several locations!
  std::string create_new_unsupported_var(std::string type_name, bool no_rename=false); // Common to all
  /* End of unsupported data for refinement info and data */

  // Common to all
  std::set<PTRef>* getVars(); // Get all variables from literals for the counter example phase
  std::string getSimpleHeader(); // Get all the declarations without the variables

  SymRef get_smt_func_decl(const char* op, SRef& in_dt, vec<SRef>& out_dt); // common to all

  std::string getStringSMTlibDatatype(const exprt& expr);
  virtual std::string getStringSMTlibDatatype(const typet& type)=0;
  SRef getSMTlibDatatype(const exprt& expr);
  virtual SRef getSMTlibDatatype(const typet& type)=0;

  void init_unsupported_counter() { unsupported2var=0; } // KE: only for re-init solver use. Once we have pop in OpenSMT, please discard.

  virtual exprt get_value(const exprt &expr) override;

  /****************** Conversion methods - methods for converting expressions to OpenSMT's PTRefs ***************/
protected:
    virtual PTRef expression_to_ptref(const exprt& expr) = 0;

    PTRef get_from_cache(const exprt& expr) const;

    void store_to_cache(const exprt& expr, PTRef ptref);

    virtual PTRef symbol_to_ptref(const exprt& expr);

    virtual PTRef new_num_var(const std::string & var_name) = 0;

    virtual PTRef new_bool_var(const std::string& var_name) {
        return logic->mkBoolVar(var_name.c_str());
    }

    virtual PTRef constant_to_ptref(const exprt& expr);

    PTRef constant_bool(bool val) const {
        return val ? logic->getTerm_true() : logic->getTerm_false();
    }

    virtual PTRef complex_symbol_to_ptref(const exprt& expr);

    virtual PTRef type_cast(const exprt & expr) = 0;

    virtual PTRef numeric_constant(const exprt &expr) = 0;

    virtual void add_symbol_constraints(const exprt &expr, const PTRef var) {}

  /* ***************************************************************************************************************/


protected:

  vec<SymRef> function_formulas;

  using expr_hasht = irep_hash;
  //using expr_hasht = irep_full_hash;
  std::unordered_map<exprt, PTRef, expr_hasht> unsupported_expr2ptrefMap;
  std::unordered_map<exprt, PTRef, expr_hasht> expression_to_ptref_map;

  static unsigned unsupported2var; // Create a new var hifrog::c::unsupported_op2var#i - smtcheck_opensmt2t::_unsupported_var_str
    std::map<std::string,SymRef> decl_uninterperted_func;

  void store_new_unsupported_var(const exprt& expr, const PTRef var); // common to all

  // virtual literalt lunsupported2var(const exprt &expr)=0; // for isnan, mod, arrays ect. that we have no support (or no support yet) create over-approx as nondet
  virtual PTRef unsupported_to_var(const exprt & expr) = 0;

  PTRef create_equation_for_unsupported(const exprt &expr); // common to all

  SymRef get_unsupported_op_func(const exprt &expr, const vec<PTRef>& args); // common to all

  void get_unsupported_op_args(const exprt &expr, vec<PTRef> &args); // common to all

  literalt push_variable(PTRef ptl); // Common to all

  PTRef mkFun(SymRef decl, const vec<PTRef>& args); // Common to all



#ifdef PRODUCE_PROOF
  void setup_reduction();

  void setup_interpolation();

  void setup_proof_transformation();

#endif

  virtual bool can_have_non_linears() {return true;}

  virtual bool is_non_linear_operator(PTRef tr)=0;

  virtual void freeSolver() override; // Common to all

  void fill_vars(PTRef, std::map<std::string, PTRef>&); // Common to all

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

  // build the string of the upper and lower bounds
  std::string create_bound_string(std::string base, int exp);

public:
//  char* getPTermString(const literalt &l) { return getPTermString(ptrefs[l.var_no()]); }
//  char* getPTermString(const exprt &expr) {
//	  if(converted_exprs.find(expr.hash()) != converted_exprs.end())
//		  return getPTermString(converted_exprs[expr.hash()]);
//	  return 0;
//  }

  void insert_substituted(const itpt & itp, const std::vector<symbol_exprt> & symbols) override;
};

#endif
