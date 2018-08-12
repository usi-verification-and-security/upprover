/*******************************************************************\

Module: Wrapper for OpenSMT2 - General one for SAT and SMT

\*******************************************************************/

#ifndef CPROVER_CHECK_OPENSMT2_H
#define CPROVER_CHECK_OPENSMT2_H

#include <vector>

#include <util/threeval.h>
#include <opensmt/opensmt2.h>
#include <util/std_expr.h>
#include <solvers/prop/literal.h>
#include "interpolating_solver.h"

class literalt;
class exprt;
/*
 TODO: think how to generalize this class and interpolating_solvert to be 
 * not related. Need also to change (split?) summarizing_checkert
 */

// Cache of already visited interpolant ptrefs
typedef std::map<PTRef, literalt> ptref_cachet;

// General interface for OPENSMT2 calls
class check_opensmt2t :  public interpolating_solvert
{
public:
  check_opensmt2t(bool reduction, int reduction_graph, int reduction_loops) :
      osmt  (nullptr),
      logic (nullptr),
      mainSolver (nullptr),
#ifdef DISABLE_OPTIMIZATIONS                
      dump_queries(false),
      dump_pre_queries(false),
      pre_queries_file_name("__pre_query_default"), // .smt2 file
#endif              
      partition_count(0),
      pushed_formulas(0),
#ifdef PRODUCE_PROOF              
      itp_algorithm(itp_alg_mcmillan),
      itp_euf_algorithm(itp_euf_alg_strong),
      itp_lra_algorithm(itp_lra_alg_strong),
      itp_lra_factor(nullptr),
      reduction(reduction),
      reduction_graph(reduction_graph),
      reduction_loops(reduction_loops),
#endif
      random_seed(1),
      verbosity(0),
      certify(0)
  { }
  
  virtual ~check_opensmt2t() {
      //if (osmt) delete osmt;
      // KE: not created here, so don't free it here!
      // This is common to all logics: prop, lra, qfuf, qfcuf
  }

    virtual literalt bool_expr_to_literal(const exprt & expr) = 0;
    virtual bool solve() = 0;
    virtual literalt land(literalt l1, literalt l2) = 0;
    virtual literalt lor(literalt l1, literalt l2) = 0;
    virtual literalt lor(const bvt & bv) = 0;

    literalt limplies(literalt a, literalt b)
    {
        return lor(!a, b);
    }
    virtual void set_equal(literalt l1, literalt l2) = 0;

    // assert this clause to the solver
    virtual void lcnf(const std::vector<literalt> & lits) = 0;

    template<typename Container>
    void assert_literals(const Container& c){
        for(auto lit : c){
            assert_literal(lit);
        }
    }

    virtual void assert_literal(literalt) = 0;

    void set_to_true(const exprt &expr) {
        literalt l = bool_expr_to_literal(expr);
        assert_literal(l);
    }

    void set_to_false(const exprt &expr){
        literalt l = bool_expr_to_literal(expr);
        assert_literal(!l); // assert the negation
    }

    void convert(const std::vector<literalt> &bv, vec<PTRef> &args);

    PTRef literalToPTRef(literalt l) {
        if(l.is_constant()){
            return l.is_true() ? getLogic()->getTerm_true() : getLogic()->getTerm_false();
        }
//        std::cout << "Literal: " << l << '\n';
//        std::cout << "PTref size: " << ptrefs.size() << '\n';
        assert(l.var_no() < ptrefs.size());
        assert(l.var_no() != literalt::unused_var_no());
        PTRef ptref = ptrefs[l.var_no()];
        return l.sign() ? getLogic()->mkNot(ptref) : ptref;
    }

    literalt get_const_literal(bool val){
        return const_literal(val);
    }

    //  Mapping from variable indices to their PTRefs in OpenSMT
    std::vector<PTRef> ptrefs;



#ifdef PRODUCE_PROOF  
  /* General method to set OpenSMT2 */
  void set_itp_bool_alg(int x)
  {
      itp_algorithm.x = x;
  }
  
  void set_itp_euf_alg(int x)
  {
      itp_euf_algorithm.x = x;
  }

  void set_itp_lra_alg(int x)
  {
      itp_lra_algorithm.x = x;
  }

  void set_itp_lra_factor(const char * f)
  {
      itp_lra_factor = f;
  }
  
  void set_reduce_proof(bool r) { reduction = r; }
  void set_reduce_proof_graph(int r) { reduction_graph = r; }
  void set_reduce_proof_loops(int r) { reduction_loops = r; }
#endif
  
  void set_random_seed(unsigned int i)
  {
    random_seed = i;
    if (osmt != nullptr) {
        const char* msg=nullptr;
        osmt->getConfig().setOption(SMTConfig::o_random_seed, SMTOption((int)random_seed), msg);
        if (msg != nullptr) free((char *)msg); // If there is an error consider printing the msg
    }
  }

  unsigned get_random_seed()
  {
      return random_seed;
  }

#ifdef DISABLE_OPTIMIZATIONS  
  void set_dump_query(bool f)
  {
    if (osmt != nullptr) {
        const char* msg=nullptr;
        osmt->getConfig().setOption(SMTConfig::o_dump_query, SMTOption(f), msg);
    }
    
    dump_queries = f;
  }
  bool get_dump_queries() { return dump_queries;}

  void set_dump_query_name(const string& n)
  {
      if (osmt != nullptr) {
          osmt->getConfig().set_dump_query_name(n.c_str());
      }
      
      pre_queries_file_name = "__preq_" + n;
  }
  
  void set_dump_pre_query(bool f) { dump_pre_queries = f;}
  bool get_dump_pre_query() { return dump_pre_queries;}
#endif

  MainSolver * getMainSolver() { return mainSolver; }

  Logic * getLogic() { return logic; }

  void set_verbosity(int r) { verbosity = r; }
  
  void set_certify(int r) { certify = r; }

    fle_part_idt new_partition() override;

    void close_partition();

    virtual bool is_overapproximating() const = 0;

    virtual bool is_assignment_true(literalt a) const = 0;

    virtual exprt get_value(const exprt &expr) = 0;

    virtual void insert_substituted(const itpt & itp, const std::vector<symbol_exprt> & symbols) = 0;


    /* General consts for prop version */
  const char* false_str = "false";
  const char* true_str = "true";
  
protected:
    void insert_top_level_formulas();

    void produceConfigMatrixInterpolants (const std::vector< std::vector<int> > &configs,
            std::vector<PTRef> &interpolants) const;

  // Initialize the OpenSMT context
  virtual void initializeSolver(const char*)=0;

  // Free context/data in OpenSMT
  virtual void freeSolver()=0;

  // Common Data members
  Opensmt* osmt;
  Logic* logic;
  MainSolver* mainSolver;

#ifdef DISABLE_OPTIMIZATIONS  
  // Dump all queries?
  bool dump_queries;
  bool dump_pre_queries;
  std::string pre_queries_file_name;
#endif  

  // Count of the created partitions; This is used by HiFrog to id a partition; correspondence with OpenSMT partitions needs to be kept!
  unsigned partition_count;

  //  List of clauses that are part of this partition (a.k.a. assert in smt2lib)
  std::vector<PTRef> current_partition;

  // Flag indicating if last partition has been closed properly
  bool last_partition_closed = true;

    /** These correspond to partitions of OpenSMT (top-level assertions);
     * INVARIANT: top_level_formulas.size() == partition_count (after closing current partition)
     */
    vec<PTRef> top_level_formulas;

    // boundary index for top_level_formulas that has been pushed to solver already
    unsigned pushed_formulas;
  
#ifdef PRODUCE_PROOF   
  // 1 - stronger, 2 - weaker (GF: not working at the moment)
  int proof_trans;

  // itp_alg_mcmillan, itp_alg_pudlak, itp_alg_mcmillanp, etc...
  ItpAlgorithm itp_algorithm;
  ItpAlgorithm itp_euf_algorithm;
  ItpAlgorithm itp_lra_algorithm;
  const char * itp_lra_factor;

  // OpenSMT2 Params
  bool reduction;
  int reduction_graph;
  int reduction_loops;

    // Can we interpolate?
  bool ready_to_interpolate;
#endif
  
  unsigned random_seed;

  int verbosity;

  int certify;
  
};

#endif
