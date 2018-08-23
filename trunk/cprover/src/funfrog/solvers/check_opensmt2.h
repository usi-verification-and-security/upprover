/*******************************************************************\

Module: Wrapper for OpenSMT2 - General one for SAT and SMT

\*******************************************************************/

#ifndef CPROVER_CHECK_OPENSMT2_H
#define CPROVER_CHECK_OPENSMT2_H

#include <vector>

#include <util/threeval.h>
#include <opensmt/opensmt2.h>
#include "funfrog/interface/solver/interpolating_solver.h"
#include "funfrog/interface/solver/solver.h"

// Cache of already visited interpolant ptrefs
typedef std::map<PTRef, literalt> ptref_cachet;

// General interface for OPENSMT2 calls
class check_opensmt2t :  public interpolating_solvert, public solvert
{
public:
  check_opensmt2t(bool _reduction, unsigned int _reduction_graph, unsigned int _reduction_loops
#ifdef DISABLE_OPTIMIZATIONS          
        , bool _dump_queries, bool _dump_pre_queries, std::string _dump_query_name
#endif
        );
  
  virtual ~check_opensmt2t();
  
  virtual void set_random_seed(unsigned int i);

  virtual unsigned get_random_seed() { return random_seed; }

  virtual  void set_verbosity(int r) { verbosity = r; }
  
  virtual  void set_certify(int r) override { certify = r; }
  
    virtual bool read_formula_from_file(std::string fileName) // KE: Sepideh, this shall be renamed according to the new interface
    { return mainSolver->readFormulaFromFile(fileName.c_str()); }
  
    virtual void dump_header_to_file(std::ostream& dump_out) 
    { logic->dumpHeaderToFile(dump_out); }
  
    virtual bool is_overapprox_encoding() const
    { return (has_unsupported_vars() && !has_overappox_mapping());}

    fle_part_idt new_partition() override;

    void close_partition();
    
  /* General consts for prop version */
  static const char* false_str;
  static const char* true_str;

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
  // 1 - stronger, 2 - weaker (GF: not working at the moment)
  int proof_trans;

  // itp_alg_mcmillan, itp_alg_pudlak, itp_alg_mcmillanp, etc...
  ItpAlgorithm itp_algorithm;
  ItpAlgorithm itp_euf_algorithm;
  ItpAlgorithm itp_lra_algorithm;
  const char * itp_lra_factor;

  // OpenSMT2 Params
  bool reduction;
  unsigned int reduction_graph;
  unsigned int reduction_loops;

    // Can we interpolate?
  bool ready_to_interpolate;
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

    void produceConfigMatrixInterpolants (const std::vector< std::vector<int> > &configs,
            std::vector<PTRef> &interpolants);

    // Initialize the OpenSMT context
    virtual void initializeSolver(const char*)=0;

    // Free context/data in OpenSMT
    virtual void freeSolver()=0;
  
    virtual bool has_unsupported_vars() const=0;
    virtual bool has_overappox_mapping() const=0;
};

#endif
