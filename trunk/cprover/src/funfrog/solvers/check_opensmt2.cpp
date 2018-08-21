#include "check_opensmt2.h"

const char* check_opensmt2t::false_str = "false";
const char* check_opensmt2t::true_str = "true";
  
check_opensmt2t::check_opensmt2t(bool _reduction, unsigned int _reduction_graph, unsigned int _reduction_loops
#ifdef DISABLE_OPTIMIZATIONS          
          , bool _dump_queries, bool _dump_pre_queries, std::string _dump_query_name
#endif
      ) :
      osmt  (nullptr),
      logic (nullptr),
      mainSolver (nullptr),              
      partition_count(0),
      current_partition(nullptr),
#ifdef PRODUCE_PROOF              
      itp_algorithm(itp_alg_mcmillan),
      itp_euf_algorithm(itp_euf_alg_strong),
      itp_lra_algorithm(itp_lra_alg_strong),
      itp_lra_factor(nullptr),
      reduction(_reduction),
      reduction_graph(_reduction_graph),
      reduction_loops(_reduction_loops),
#endif
      random_seed(1),
      verbosity(0),
      certify(0)
#ifdef DISABLE_OPTIMIZATIONS
      , dump_queries(_dump_queries)
      , dump_pre_queries(_dump_pre_queries)
      , pre_queries_file_name(_dump_query_name) // .smt2 file       
#endif
{ 
#ifdef DISABLE_OPTIMIZATIONS    
    set_dump_query(dump_queries);
    set_dump_query_name(pre_queries_file_name);
#endif
}

// Not in use
check_opensmt2t::~check_opensmt2t() 
{
    //if (osmt) delete osmt;
    // KE: not created here, so don't free it here!
    // This is common to all logics: prop, lra, qfuf, qfcuf
}

void check_opensmt2t::set_random_seed(unsigned int i)
{
  random_seed = i;
  if (osmt != nullptr) {
      const char* msg=nullptr;
      osmt->getConfig().setOption(SMTConfig::o_random_seed, SMTOption((int)random_seed), msg);
      if (msg != nullptr) free((char *)msg); // If there is an error consider printing the msg
  }
}

#ifdef DISABLE_OPTIMIZATIONS 
// Code for init these options
void check_opensmt2t::set_dump_query(bool f)
{
  if (osmt != nullptr) {
      const char* msg=nullptr;
      osmt->getConfig().setOption(SMTConfig::o_dump_query, SMTOption(f), msg);
  }

  dump_queries = f;
}

void check_opensmt2t::set_dump_query_name(const string& n)
{
    if (osmt != nullptr) {
        osmt->getConfig().set_dump_query_name(n.c_str());
    }

    base_dump_query_name = n;
    pre_queries_file_name = "__preq_" + base_dump_query_name;
}
#endif