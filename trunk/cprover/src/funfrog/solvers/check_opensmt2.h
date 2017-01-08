/*******************************************************************\

Module: Wrapper for OpenSMT2 - General one for SAT and SMT

\*******************************************************************/

#ifndef CPROVER_CHECK_OPENSMT2_H
#define CPROVER_CHECK_OPENSMT2_H

#include <vector>

#include <solvers/sat/cnf.h>
#include <util/threeval.h>
#include <opensmt/opensmt2.h>

// Cache of already visited interpolant ptrefs
typedef std::map<PTRef, literalt> ptref_cachet;

// General interface for OPENSMT2 calls
class check_opensmt2t
{
public:
  check_opensmt2t() :
      osmt  (NULL),
      logic (NULL),
      mainSolver (NULL),
      dump_queries(false),
      partition_count(0),
      current_partition(0),
      itp_algorithm(itp_alg_mcmillan),
      itp_euf_algorithm(itp_euf_alg_strong),
      itp_lra_algorithm(itp_lra_alg_strong),
      itp_lra_factor(NULL)
  { }
  
  virtual ~check_opensmt2t() { }

  virtual prop_conv_solvert* get_prop_conv_solver()=0;
  
  
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

  
  /* General consts for prop version */
  const char* false_str = "false";
  const char* true_str = "true";

protected:
  // Initialize the OpenSMT context
  virtual void initializeSolver()=0;

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
  
  
  // OpenSMT2 Params
  bool reduction;
  int reduction_loops;
  int reduction_graph;

  // itp_alg_mcmillan, itp_alg_pudlak, itp_alg_mcmillanp, etc...
  ItpAlgorithm itp_algorithm;
  ItpAlgorithm itp_euf_algorithm;
  ItpAlgorithm itp_lra_algorithm;
  const char * itp_lra_factor;

};

#endif
