/*******************************************************************\

Module: Wrapper for OpenSMT2

\*******************************************************************/

#ifndef CPROVER_SMTCHECK_PERIPLO_H
#define CPROVER_SMTCHECK_PERIPLO_H

//#define DEBUG_SMT_LRA

#include <map>
#include <vector>

#include <solvers/sat/cnf.h>
#include <util/threeval.h>
#include "interpolating_solver.h"
#include <opensmt/opensmt2.h>
#include <expr.h>


// Cache of already visited interpolant literals
typedef std::map<PTRef, literalt> ptref_cachet;

class smtcheck_opensmt2t : public interpolating_solvert
{
public:
  smtcheck_opensmt2t() :
      osmt  (NULL),
      logic (NULL),
      mainSolver (NULL),
      dump_queries(true),
      partition_count(0),
      no_literals(0),
      itp_algorithm(itp_alg_mcmillan),
	  pushed_formulas(0),
	  current_partition(0),
	  unsupported2var(0)
  {
    initializeSolver();
  }

  virtual ~smtcheck_opensmt2t(); // d'tor

  bool solve();
  
  tvt get_assignemt(literalt a) const;

  literalt convert(const exprt &expr);

  void set_to_true(const exprt &expr);
  void set_to_true(PTRef);

  void set_equal(literalt l1, literalt l2);

  PTRef convert_symbol(const exprt &expr);

  literalt const_var(bool val);

  literalt const_var_Real(const exprt &expr);

  literalt type_cast(const exprt &expr);

  literalt limplies(literalt l1, literalt l2);

  literalt lnotequal(literalt l1, literalt l2);

  literalt land(literalt l1, literalt l2);

  literalt land(bvt b);

  literalt lor(literalt l1, literalt l2);

  literalt lor(bvt b);

  literalt lnot(literalt l);

  literalt lvar(const exprt &expr);

  literalt lconst(const exprt &expr);

  fle_part_idt new_partition();

  void get_interpolant(const interpolation_taskt& partition_ids,
      interpolantst& interpolants);

  bool can_interpolate() const;

  // Extract interpolant form OpenSMT files/data
  //void extract_itp(PTRef ptref, prop_itpt& target_itp) const;
  void extract_itp(PTRef ptref, smt_itpt& target_itp) const;

  void adjust_function(smt_itpt& itp, std::vector<symbol_exprt>& common_symbols, std::string fun_name);

  static int get_index(const string& varname);
  static std::string quote_varname(const string& varname);
  static std::string unquote_varname(const string& varname);
  
  static std::string remove_index(std::string);
  static std::string remove_invalid(const string& varname);

  static bool is_quoted_var(const string& varname);

  MainSolver * getMainSolver() { return mainSolver; }

  LRALogic * getLRALogic() { return logic; }

  /* KE : remove, will use OpenSMT code + PTRefs in hifrog
  // Simple recursive extraction of clauses from OpenSMT Egraph
  literalt extract_itp_rec(PTRef ptref, prop_itpt& target_itp,
    ptref_cachet& ptref_cache) const;
   *
   */

  const char* false_str = "false";
  const char* true_str = "true";

  void start_encoding_partitions() {
	  if (partition_count > 0){
		  if (ready_to_interpolate) cout << "EXIT WITH ERROR: Try using --claim parameter" << std::endl;
		  assert (!ready_to_interpolate); // GF: checking of previous assertion run was successful (unsat)
		  	  	  	  	  	  	  	  	  // TODO: reset opensmt context

		  std::cout << "Incrementally adding partitions to the SMT solver\n";
	  }
  }

protected:

  Opensmt* osmt;
  LRALogic* logic;
  MainSolver* mainSolver;
  vec<PTRef> top_level_formulas;

  map<size_t, literalt> converted_exprs;


  bool dump_queries;

  unsigned partition_count;

  bool ready_to_interpolate;
  
  unsigned no_literals;

  int reduction_loops;

  int reduction_graph;

  // itp_alg_mcmillan, itp_alg_pudlak, itp_alg_mcmillanp, etc...
  ItpAlgorithm itp_algorithm;

  // 1 - stronger, 2 - weaker (GF: not working at the moment)
  int proof_trans;

//  List of clauses that are part of this partition (a.k.a. assert in smt2lib)
  vec<PTRef>* current_partition;

//  Mapping from boolean variable indexes to their PTRefs
  std::vector<PTRef> literals;

  unsigned pushed_formulas;

  unsigned unsupported2var; // Create a new var funfrog::c::unsupported_op2var#i

  literalt lunsupported2var(exprt expr); // for isnan, mod, arrays ect. that we have no support (or no support yet) create over-approx as nondet

  literalt new_variable();

  literalt push_variable(PTRef ptl);

  void setup_reduction();

  void setup_interpolation();

  void setup_proof_transformation();
  
  void initializeSolver();

  void produceConfigMatrixInterpolants (const vector< vector<int> > &configs, vector<PTRef> &interpolants);

  void close_partition();

  void freeSolver();

  std::string extract_expr_str_number(const exprt &expr); // Our conversion of const that works also for negative numbers + check of result

  std::pair <std::string, bool> extract_expr_str_number_wt_sign(const exprt &expr); // Fix problems with declare of negative numbers

  std::string extract_expr_str_name(const exprt &expr); // General method for extracting the name of the var

  bool isLinearOp(const exprt &expr, vec<PTRef> &args); // Check if we don't do sth. like nondet*nondet, but only const*nondet (e.g.)

  void fill_vars(PTRef, std::map<std::string, PTRef>&);

  void dump_on_error(std::string location);

private:
  // Basic prints for debug - KE: Hope I did it right :-)
  char* getPTermString(const PTRef &term) { return logic->printTerm(term);}

#ifdef DEBUG_SMT_LRA
  std::map <std::string,std::string> ite_map_str;
  std::set <std::string> var_set_str;
  typedef std::map<std::string,std::string>::iterator it_ite_map_str;
  typedef std::set<std::string>::iterator it_var_set_str;

  std::string getVarData(const PTRef &var) {
	  return string(logic->getSortName(logic->getSortRef(var)));
  }
#endif
public:
  char* getPTermString(const literalt &l) { return getPTermString(literals[l.var_no()]); }
  char* getPTermString(const exprt &expr) {
	  if(converted_exprs.find(expr.hash()) != converted_exprs.end())
		  return getPTermString(converted_exprs[expr.hash()]);
	  return 0;
  }
};

#endif
