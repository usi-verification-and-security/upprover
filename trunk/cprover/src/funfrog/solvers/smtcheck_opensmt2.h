/*******************************************************************\

Module: Wrapper for OpenSMT2

\*******************************************************************/

#ifndef CPROVER_SMTCHECK_PERIPLO_H
#define CPROVER_SMTCHECK_PERIPLO_H

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
      itp_algorithm(1)
  {
    initializeSolver();
  }

  bool solve();
  
  tvt get_assignemt(literalt a) const;

  literalt convert(const exprt &expr);

  void set_to_true(const exprt &expr);

  void set_equal(literalt l1, literalt l2);

  literalt const_var(bool val);

  literalt const_var_Real(const exprt &expr);

  literalt const_var_Real(std::string val);

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

  /* KE : remove, will use OpenSMT code + PTRefs in hifrog
  // Simple recursive extraction of clauses from OpenSMT Egraph
  literalt extract_itp_rec(PTRef ptref, prop_itpt& target_itp,
    ptref_cachet& ptref_cache) const;
   *
   */

  const char* false_str = "false";
  const char* true_str = "true";

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

  // 0 - Pudlak, 1 - McMillan, 2 - McMillan'
  int itp_algorithm;

  // 1 - stronger, 2 - weaker (GF: not working at the moment)
  int proof_trans;

//  List of clauses that are part of this partition (a.k.a. assert in smt2lib)
  vec<PTRef>* current_partition;

//  Mapping from boolean variable indexes to their PTRefs
  std::vector<PTRef> literals;

  literalt new_variable();

  void setup_reduction();

  void setup_interpolation();

  void setup_proof_transformation();
  
  void initializeSolver();

  void produceConfigMatrixInterpolants (const vector< vector<int> > &configs, vector<PTRef> &interpolants);

  void close_partition();

  void freeSolver();

  std::string extract_expr_str_number(const exprt &expr); // Our conversion of const that works also for negative numbers + check of result

  std::string extract_expr_str_name(const exprt &expr); // General method for extracting the name of the var

  std::string remove_index(std::string);
  void fill_vars(PTRef, std::map<std::string, PTRef>&);


  // Basic prints for debug - KE: Hope I did it right :-)
private:
  char* getPTermString(const PTRef &term) { return logic->printTerm(term);}
public:
  char* getPTermString(const literalt &l) { return getPTermString(literals[l.get()]); }
  char* getPTermString(const exprt &expr) {
	  if(converted_exprs.find(expr.full_hash()) != converted_exprs.end())
		  return getPTermString(converted_exprs[expr.full_hash()]);
	  return 0;
  }
};

#endif
