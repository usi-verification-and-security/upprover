/*******************************************************************\

Module: Wrapper for OpenSMT2 - General one for SAT and SMT

\*******************************************************************/

#ifndef CPROVER_CHECK_OPENSMT2_H
#define CPROVER_CHECK_OPENSMT2_H

#include <vector>

#include <solvers/sat/cnf.h>
#include <util/threeval.h>
#include <opensmt/opensmt2.h>
#include "interpolating_solver.h"

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
      osmt  (NULL),
      logic (NULL),
      mainSolver (NULL),
      dump_queries(false),
      partition_count(0),
      current_partition(0),
#ifdef PRODUCE_PROOF              
      itp_algorithm(itp_alg_mcmillan),
      itp_euf_algorithm(itp_euf_alg_strong),
      itp_lra_algorithm(itp_lra_alg_strong),
      itp_lra_factor(NULL),
      reduction(reduction),
      reduction_graph(reduction_graph),
      reduction_loops(reduction_loops),
#endif
      random_seed(1),
      verbosity(0),
      certify(0)
  { }
  
  virtual ~check_opensmt2t() { }

  virtual prop_conv_solvert* get_prop_conv_solver()=0;
  

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
    if (osmt != NULL) {
        const char* msg=NULL;
        osmt->getConfig().setOption(SMTConfig::o_random_seed, SMTOption((int)random_seed), msg);
        if (msg != NULL) free((char *)msg); // If there is an error consider printing the msg
    }
  }


  unsigned get_random_seed()
  {
      return random_seed;
  }

  void set_dump_query(bool f)
  {
    if (osmt != NULL) {
        const char* msg=NULL;
        osmt->getConfig().setOption(SMTConfig::o_dump_query, SMTOption(f), msg);
//        if (msg != NULL) free((char *)msg); // If there is an error consider printing the msg
    }
  }

  MainSolver * getMainSolver() { return mainSolver; }

  Logic * getLogic() { return logic; }

  void set_verbosity(int r) { verbosity = r; }
  
  void set_certify(int r) { certify = r; }
  
  /* General consts for prop version */
  const char* false_str = "false";
  const char* true_str = "true";
  
protected:
  // Initialize the OpenSMT context
  virtual void initializeSolver(const char*)=0;

  // Free context/data in OpenSMT
  virtual void freeSolver()=0;

  // Common Data members
  Opensmt* osmt;
  Logic* logic;
  MainSolver* mainSolver;

  // Dump all queries?
  bool dump_queries;

  // Count of the created partitions
  unsigned partition_count;

  //  List of clauses that are part of this partition (a.k.a. assert in smt2lib)
  vec<PTRef>* current_partition;
  
#ifdef PRODUCE_PROOF   
  // 1 - stronger, 2 - weaker (GF: not working at the moment)
  int proof_trans;  
  
  // OpenSMT2 Params
  bool reduction;
  int reduction_loops;
  int reduction_graph;

  // itp_alg_mcmillan, itp_alg_pudlak, itp_alg_mcmillanp, etc...
  ItpAlgorithm itp_algorithm;
  ItpAlgorithm itp_euf_algorithm;
  ItpAlgorithm itp_lra_algorithm;
  const char * itp_lra_factor;
  
  // Can we interpolate?
  bool ready_to_interpolate;
#endif
  
  unsigned random_seed;

  int verbosity;

  int certify;
  
};

#endif
