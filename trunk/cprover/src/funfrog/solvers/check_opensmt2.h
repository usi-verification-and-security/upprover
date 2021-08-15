/***s****************************************************************\

Module: Wrapper for OpenSMT2 - General one for SAT and SMT

\*******************************************************************/

#ifndef CPROVER_CHECK_OPENSMT2_H
#define CPROVER_CHECK_OPENSMT2_H

#include <util/threeval.h>
#include <opensmt/opensmt2.h>
#include <util/std_expr.h>
#include <solvers/prop/literal.h>
#include "funfrog/interface/solver/interpolating_solver.h"
#include "funfrog/interface/solver/solver.h"
#include "solver_options.h"
#include "funfrog/interface/convertor.h"
#include "funfrog/interface/ssa_solvert.h"

#include <vector>

class exprt;

// Cache of already visited interpolant ptrefs
typedef std::map<PTRef, literalt> ptref_cachet;

// General interface for OPENSMT2 calls
class check_opensmt2t :  public interpolating_solvert, public solvert, public convertort, public ssa_solvert
{
public:
    check_opensmt2t();
          
    virtual ~check_opensmt2t();
    
    void reset_solver() override {
        mainSolver.reset(new MainSolver(*logic, *config, "opensmt"));
    }
    // ********************* methods implementing ssa_solvert interface ***************************************
#ifdef PRODUCE_PROOF
    interpolating_solvert* get_interpolating_solver() override { return this; }
#endif // PRODUCE_PROOF
    solvert* get_solver() override { return this; }

    convertort* get_convertor() override { return this; }
    // *********************************************************************************************************

    template<typename Container>
    void assert_literals(const Container& c){
        for(auto lit : c){
            assert_literal(lit);
        }
    }

    void set_to_true(const exprt &expr) override {
        auto l = convert_bool_expr(expr);
        assert_literal(l);
    }

    void set_to_false(const exprt &expr) override{
        auto l = convert_bool_expr(expr);
        assert_literal(!l); // assert the negation
    }

    Logic* getLogic() const {return logic.get();}
    
    unsigned get_random_seed() override { return random_seed; }
    
    void dump_header_to_file(std::ostream& dump_out)
    { logic->dumpHeaderToFile(dump_out); }


    fle_part_idt new_partition() override;

    void close_partition() override;

    virtual bool is_overapproximating() const = 0;

    PTRef substitute(PTRef term, Logic::SubstMap const & subst);

    /* General consts for prop version - Shall be Static. No need to allocate these all the time */
    static const char* false_str;
    static const char* true_str;

protected:
    // common Data members
    std::unique_ptr<Logic> logic;
    std::unique_ptr<MainSolver> mainSolver;
    std::unique_ptr<SMTConfig> config;
    
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

    //  Mapping from variable indices to their PTRefs in OpenSMT
    std::vector<PTRef> ptrefs;
    
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
    void set_dump_query(bool f);
    void set_dump_query_name(const string& n);
#endif 
  
    void insert_top_level_formulas();

    // Initialize the OpenSMT context
    virtual void initializeSolver(const solver_optionst, const char*)=0;
    
    virtual void set_random_seed(unsigned int i) override;
     
    // Used only in check_opensmt2 sub-classes
    PTRef flaref_to_ptref(const FlaRef fr) const {
        if(fr.is_constant()){
            return fr.is_true() ? getLogic()->getTerm_true() : getLogic()->getTerm_false();
        }
        assert(fr.no() < ptrefs.size());
        PTRef ptref = ptrefs[fr.no()];
        return fr.sign() ? getLogic()->mkNot(ptref) : ptref;
    }
};

#endif
