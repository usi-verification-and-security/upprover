/*******************************************************************\

Module: Wrapper for OpenSMT2

\*******************************************************************/

#ifndef CPROVER_SMTCHECK_OPENSMT2_H
#define CPROVER_SMTCHECK_OPENSMT2_H

#include <map>
#include <vector>

#include "../utils/unsupported_operations.h" // KE: shall move all the code of unsupported here
#include "check_opensmt2.h"
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
  // C'tor to pass the value to main interface check_opensmt2
  smtcheck_opensmt2t(bool _reduction, int _reduction_graph, int _reduction_loops, 
#ifdef DISABLE_OPTIMIZATIONS  
          bool _dump_queries, bool _dump_pre_queries, std::string _dump_query_name,
#endif              
          bool _store_unsupported_info=false) :
        check_opensmt2t(_reduction, _reduction_graph, _reduction_loops
#ifdef DISABLE_OPTIMIZATIONS  
        , _dump_queries, _dump_pre_queries, _dump_query_name 
#endif        
        ),
        no_literals(0),
        no_literals_last_solved(0),
        unsupported_info(unsupported_operationst(_store_unsupported_info))
  { /* No init of solver - done for inherit check_opensmt2 */}

  virtual ~smtcheck_opensmt2t(); // d'tor

  virtual void freeSolver() override { if (osmt != nullptr) delete osmt; }
 
  virtual bool solve(); // Common to all

  virtual bool is_assignemt_true(literalt a) const; // Common to all, refiner+error_trace

  virtual exprt get_value(const exprt &expr)=0;

  virtual literalt convert(const exprt &expr) =0;

  void set_to_false(const exprt &expr); // Common to all - dependency checker
  virtual void set_to_true(const exprt &expr); // Common to all

  virtual void set_equal(literalt l1, literalt l2); // Common to all

  virtual literalt lconst(bool val); // Common to all

  virtual literalt limplies(literalt l1, literalt l2); // Common to all

  virtual literalt land(literalt l1, literalt l2); // Common to all

  virtual literalt land(bvt b); // Common to all

  virtual literalt lor(literalt l1, literalt l2); // Common to all

  virtual literalt lor(bvt b); // Common to all

  virtual literalt lnot(literalt l); // Common to all

  virtual literalt lassert(const exprt &expr)
  { return convert(expr); }
  
#ifdef PRODUCE_PROOF
  void get_interpolant(const interpolation_taskt& partition_ids,
      interpolantst& interpolants); // Common to all

  bool can_interpolate() const; // Common to all

  // Extract interpolant form OpenSMT files/data
  void extract_itp(PTRef ptref, smt_itpt& target_itp) const; // Common to all

  virtual void generalize_summary(itpt& interpolant, std::vector<symbol_exprt>& common_symbols,
                          const std::string& fun_name, bool substitute);
#endif
  std::set<PTRef>* get_non_linears(); // Common to all, needed only if there are summaries!

  // Common to all
  virtual void start_encoding_partitions() {
	if (partition_count > 0){
#ifdef PRODUCE_PROOF
            if (ready_to_interpolate) std::cout << "EXIT WITH ERROR: Try using --claim parameter" << std::endl;
		assert (!ready_to_interpolate); // GF: checking of previous assertion run was successful (unsat)
#endif		  	  	  	  	  	  	  	  	  // TODO: reset opensmt context

		std::cout << "Incrementally adding partitions to the SMT solver\n";
	}
  }
  
  // Common to all
  std::string getSimpleHeader(); // Get all the declarations without the variables

  SymRef get_smt_func_decl(const char* op, SRef& in_dt, vec<SRef>& out_dt); // common to all

  std::string getStringSMTlibDatatype(const exprt& expr);
  virtual std::string getStringSMTlibDatatype(const typet& type)=0;
  SRef getSMTlibDatatype(const exprt& expr);
  virtual SRef getSMTlibDatatype(const typet& type)=0;
  
  virtual SRef get_sort_ref(PTRef item) { return logic->getSortRef(item); }
  
  char* getPTermString(const PTRef &term) { return logic->printTerm(term);}
  
  vec<Tterm>& get_functions() { return logic->getFunctions();} // Common to all

  void dump_function(ostream& dump_out, const Tterm& t) { logic->dumpFunction(dump_out, t); }
  
  Logic* getLogic() { return logic; }
  
  virtual void insert_substituted(const itpt & itp, const std::vector<symbol_exprt> & symbols);
  
/////////////////////////////////// Protected //////////////////////////////////  
protected:

  vec<SymRef> function_formulas;

  std::map<size_t, literalt> converted_exprs;

  unsigned no_literals;

  unsigned no_literals_last_solved; // Check if in incremental solver mode

  //  Mapping from boolean variable indexes to their PTRefs
  std::vector<PTRef> literals;
  typedef std::vector<PTRef>::iterator it_literals;

  unsupported_operationst unsupported_info;
  
  virtual bool has_unsupported_vars() const override { return unsupported_info.has_unsupported_vars(); }
  virtual bool has_overappox_mapping() const { return unsupported_info.has_unsupported_info(); }
  virtual void init_unsupported_counter() { unsupported_info.init_unsupported_counter(); }
  virtual unsupported_operationst get_unsupported_info() { return unsupported_info;}

  literalt store_new_unsupported_var(const exprt& expr, const PTRef var, bool push_var=true); // common to all

  virtual literalt lunsupported2var(const exprt &expr)=0; // for isnan, mod, arrays ect. that we have no support (or no support yet) create over-approx as nondet

  PTRef create_equation_for_unsupported(const exprt &expr); // common to all

  SymRef get_unsupported_op_func(const exprt &expr, const vec<PTRef>& args); // common to all

  void get_unsupported_op_args(const exprt &expr, vec<PTRef> &args); // common to all

  literalt new_variable(); // Common to all

  literalt push_variable(PTRef ptl); // Common to all

  PTRef mkFun(SymRef decl, const vec<PTRef>& args); // Common to all

  void set_to_true(PTRef); // Common to all

  virtual literalt lconst_number(const exprt &expr)=0;

  virtual literalt ltype_cast(const exprt &expr)=0;

  literalt lvar(const exprt &expr);
  
  virtual PTRef evar(const exprt &expr, std::string var_name)=0;
  
  literalt lconst(const exprt &expr); // Common to all, except to LRA (and LIA)

  PTRef convert_symbol(const exprt &expr); // Common to all
  
#ifdef PRODUCE_PROOF
  void setup_reduction();

  void setup_interpolation();

  void setup_proof_transformation();

#endif

  virtual bool can_have_non_linears()=0;

  virtual bool is_non_linear_operator(PTRef tr)=0;

  virtual void initializeSolver(const char*)=0;

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
        assert(v1.val != NULL);
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
  std::set <std::string> var_set_str;
  typedef std::map<std::string,std::string>::iterator it_ite_map_str;
  typedef std::set<std::string>::iterator it_var_set_str;
#endif
  void dump_on_error(std::string location);
  char* getPTermString(const literalt &l) { return getPTermString(literals[l.var_no()]); }
  char* getPTermString(const exprt &expr) {
    if(converted_exprs.find(expr.hash()) != converted_exprs.end())
        return getPTermString(converted_exprs[expr.hash()]);
    return 0;
  }
   
  // build the string of the upper and lower bounds
  std::string create_bound_string(std::string base, int exp); 
  
  // Add L2 counter to symex objects in summaries
  void add_instance_no_symex_symbol(
        Map<PTRef, PtAsgn, PTRefHash>& subst,
        const std::vector<symbol_exprt> & symbols, 
        unsigned summary_instance_no); // common to all
  
  PTRef convert_symex_symbol(std::string argument_name, unsigned summary_instance_no); // common to all
  
  virtual PTRef make_var(const std::string name)=0;
  
};

#endif
