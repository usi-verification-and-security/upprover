#include "check_opensmt2.h"
#include <solvers/prop/literal.h>

// Shall be static - no need to allocate these all the time!
const char* check_opensmt2t::false_str = "false";
const char* check_opensmt2t::true_str = "true";

check_opensmt2t::check_opensmt2t() :
      osmt  (nullptr),
      logic (nullptr),
      mainSolver (nullptr),              
      partition_count(0),
      pushed_formulas(0),
#ifdef PRODUCE_PROOF              
      itp_algorithm(itp_alg_mcmillan),
      itp_euf_algorithm(itp_euf_alg_strong),
      itp_lra_algorithm(itp_lra_alg_strong),
      itp_lra_factor("0"),
      reduction(false),
      reduction_graph(3),
      reduction_loops(2),
#endif
      random_seed(1),
      verbosity(0),
      certify(0)
{ 
#ifdef DISABLE_OPTIMIZATIONS    
    set_dump_query(false);
    set_dump_query_name("__pre_query_default");
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
  if (osmt != NULL) {
      const char* msg=nullptr;
      osmt->getConfig().setOption(SMTConfig::o_random_seed, SMTOption((int)random_seed), msg);
      if ((char *)msg != nullptr) { 
          // If there is an error consider printing the msg
          /*free((char *)msg); // KE: UNIX crash herel TODO
           ==2676== Invalid free() / delete / delete[] / realloc()
           ==2676==    at 0x4C2EDEB: free (in /usr/lib/valgrind/vgpreload_memcheck-amd64-linux.so) */
          msg=nullptr;
      }
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

void check_opensmt2t::set_dump_pre_query(bool f) {dump_pre_queries = f;}

void check_opensmt2t::set_dump_query_name(const string& n)
{
    if (osmt != nullptr) {
        osmt->getConfig().set_dump_query_name(n.c_str());
    }

    base_dump_query_name = n;
    pre_queries_file_name = "__preq_" + base_dump_query_name;
}
#endif

/*******************************************************************\

Function: check_opensmt2t::close_partition

  Inputs:

 Outputs:

 Purpose: Closes the interpolation partition by passing its CNF form
 (collected in current_partition) to the solver.

\*******************************************************************/
void check_opensmt2t::close_partition() {
    assert(!last_partition_closed);
    if (!last_partition_closed) {
        // opensmt can handle special cases like 0 or 1 argument properly
        const PTRef pand = logic->mkAnd(current_partition);
        top_level_formulas.push(pand);
        assert((unsigned)top_level_formulas.size() == partition_count);
        current_partition.clear();
        last_partition_closed = true;
#ifdef DEBUG_SMT2SOLVER
        if(current_partition.size() == 1){
          std::cout << "Trivial partition (terms size = 1): " << partition_count << "\n";
      }
      char* s= logic->printTerm(pand);
      std::cout << "; Pushing to solver: " << s << endl;
      free(s);
#endif
    }
}

/*******************************************************************\

Function: opensmt2t::new_partition

  Inputs:

 Outputs: returns a unique partition id

 Purpose: Begins a partition of formula for latter reference during
 interpolation extraction. All assertions made until
 next call of new_partition() will be part of this partition.

\*******************************************************************/
fle_part_idt check_opensmt2t::new_partition() {
    // Finish the previous partition if any
    if (!last_partition_closed) {
        assert(partition_count != 0);
        if(current_partition.empty()){
            std::cerr << "WARNING: last partition was empty (probably due to slicing)." << std::endl;
        }
        // this is the important statement in this block; before is just checking
        close_partition();
    }
    // we are creating new partition which is not closed at the moment
    last_partition_closed = false;
    return partition_count++;
}

void check_opensmt2t::insert_top_level_formulas() {
    for(auto i = pushed_formulas; i < (unsigned)top_level_formulas.size(); ++i) {
        char *msg = nullptr;
#ifdef PRODUCE_PROOF
        mainSolver->insertFormula(top_level_formulas[i], i, &msg);
#else
        mainSolver->insertFormula(top_level_formulas[i], &msg);
#endif //PRODUCE_PROOF

        if (msg != nullptr) {
            free(msg); // If there is an error, consider print msg
        }
    }
    pushed_formulas = top_level_formulas.size();
}


void check_opensmt2t::convert(const std::vector<literalt> &bv, vec<PTRef> &args)
{
    for(const auto & lit : bv) {
        // we never use 'unused_var_no' (cnf.cpp)
        assert(lit.var_no()!=literalt::unused_var_no());

        PTRef var = literalToPTRef(lit);
        args.push(var);
    }
}

#ifdef PRODUCE_PROOF

void check_opensmt2t::produceConfigMatrixInterpolants(const std::vector<std::vector<int> > & configs,
                                                      std::vector<PTRef> & interpolants) const {
    SimpSMTSolver& solver = osmt->getSolver();

    // First interpolant is true -> all partitions in B
    for ( unsigned i = 0; i < configs.size(); i++ )
    {
        ipartitions_t mask = 0;
        for (unsigned j = 0; j < configs[i].size(); j++)
        {
            setbit ( mask, configs[i][j]);
        }
        solver.getSingleInterpolant(interpolants, mask);
    }
}

#endif
