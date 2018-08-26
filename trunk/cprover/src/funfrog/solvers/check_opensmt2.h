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
#include "funfrog/interface/solver/interpolating_solver.h"
#include "funfrog/interface/solver/solver.h"
#include "funfrog/interface/convertor.h"

//class literalt;  //SA: Is not this declaration redundant?
class exprt;

// Cache of already visited interpolant ptrefs
typedef std::map<PTRef, literalt> ptref_cachet;

// General interface for OPENSMT2 calls
class check_opensmt2t :  public interpolating_solvert, public solvert, public convertort
{
public:
    check_opensmt2t();
    check_opensmt2t(bool _reduction, unsigned int _reduction_graph, unsigned int _reduction_loops) : check_opensmt2t()
    {
        set_reduction(_reduction);
        set_reduction_graph(_reduction_graph);
        set_reduction_loops(_reduction_loops);
    }

    virtual ~check_opensmt2t();

    virtual literalt bool_expr_to_literal(const exprt & expr) = 0;
    // virtual literalt land(literalt l1, literalt l2) = 0;  //moved to iface
    virtual literalt lor(literalt l1, literalt l2) = 0;
    virtual literalt lor(const bvt & bv) = 0;
    virtual literalt get_and_clear_var_constraints() { return const_literal(true); }

    literalt limplies(literalt a, literalt b)
    {
        return lor(!a, b);
    }
    // virtual void set_equal(literalt l1, literalt l2) = 0;  //SA: moved to interface class convertort

    // assert this clause to the solver
    virtual void lcnf(const std::vector<literalt> & lits) = 0;

    template<typename Container>
    void assert_literals(const Container& c){
        for(auto lit : c){
            assert_literal(lit);
        }
    }

    virtual void assert_literal(literalt) = 0;

    void set_to_true(const exprt &expr) override {
        literalt l = bool_expr_to_literal(expr);
        assert_literal(l);
    }

    void set_to_false(const exprt &expr){
        literalt l = bool_expr_to_literal(expr);
        assert_literal(!l); // assert the negation
    }

    Logic* getLogic() {return logic;}

    void convert(const std::vector<literalt> &bv, vec<PTRef> &args);

    PTRef literalToPTRef(literalt l) {
        if(l.is_constant()){
            return l.is_true() ? getLogic()->getTerm_true() : getLogic()->getTerm_false();
        }
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
  

    void set_random_seed(unsigned int i)override;

    unsigned get_random_seed() override { return random_seed; }

    void set_verbosity(int r) override { verbosity = r; }
  
    void set_certify(int r) override { certify = r; }
  
    bool read_formula_from_file(std::string fileName) // KE: Sepideh, this shall be renamed according to the new interface
    { return mainSolver->readFormulaFromFile(fileName.c_str()); }
  
    void dump_header_to_file(std::ostream& dump_out)
    { logic->dumpHeaderToFile(dump_out); }

    vec<Tterm> & get_functions() { return getLogic()->getFunctions();}
  
    virtual bool is_overapprox_encoding() const = 0;

    expr_idt new_partition() override;

    void close_partition() override;

    virtual bool is_overapproximating() const = 0;

   // virtual bool is_assignment_true(literalt a) const = 0; //SA: moved to the interface class solvert

   // virtual exprt get_value(const exprt &expr) = 0;  //SA: moved to the interface class solvert

    //virtual void insert_substituted(const itpt & itp, const std::vector<symbol_exprt> & symbols) = 0; //SA: moved to interface interpolating_solver

    /* General consts for prop version */
  const char* false_str = "false";
  const char* true_str = "true";

#ifdef PRODUCE_PROOF
    //virtual void generalize_summary(itpt * interpolant, std::vector<symbol_exprt> & common_symbols) = 0; //SA:moved to interface

    void set_reduction(bool do_reduction) { reduction = do_reduction; }
    void set_reduction_graph(unsigned int _reduction_graph) { reduction_graph = _reduction_graph; }
    void set_reduction_loops(unsigned int _reduction_loops) { reduction_loops = _reduction_loops; }

    void set_prop_itp_alg(ItpAlgorithm itp) {itp_algorithm = itp;}

    // TODO: move these options to appropriate suclasses
    void set_lra_itp_alg(ItpAlgorithm lra_itp) {itp_lra_algorithm = lra_itp;}
    void set_uf_itp_alg(ItpAlgorithm uf_itp) {itp_euf_algorithm = uf_itp;}
    void set_lra_factor(std::string factor) {itp_lra_factor = std::move(factor);}

#endif //PRODUCE_PROOF

#ifdef DISABLE_OPTIMIZATIONS
    void set_dump_query(bool f);
    void set_dump_pre_query(bool f);
    void set_dump_query_name(const string& n);
#endif // DISABLE_OPTIMIZATIONS

protected:
  // Common Data members
  Opensmt* osmt;
  Logic* logic;
  MainSolver* mainSolver; 

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
  // itp_alg_mcmillan, itp_alg_pudlak, itp_alg_mcmillanp, etc...
  ItpAlgorithm itp_algorithm;
  ItpAlgorithm itp_euf_algorithm;
  ItpAlgorithm itp_lra_algorithm;
  std::string itp_lra_factor;

  // OpenSMT2 Params
  bool reduction;
  unsigned int reduction_graph;
  unsigned int reduction_loops;

    // Can we interpolate?
  bool ready_to_interpolate;

    void produceConfigMatrixInterpolants (const std::vector< std::vector<int> > &configs,
                                          std::vector<PTRef> &interpolants) const;
#endif
  
  unsigned random_seed;

  int verbosity;

  int certify;
  
#ifdef DISABLE_OPTIMIZATIONS
  // Dump all queries?
  bool dump_queries;
  bool dump_pre_queries;
  std::string base_dump_query_name;
  std::string pre_queries_file_name;

  // Code for init these options

#endif 
  
    void insert_top_level_formulas();

    // Initialize the OpenSMT context
    virtual void initializeSolver(const char*)=0;

    // Free context/data in OpenSMT
    virtual void freeSolver() { delete osmt; osmt = nullptr; }
};

#endif
