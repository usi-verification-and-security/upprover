#include "check_opensmt2.h"
#include <solvers/prop/literal.h>

#include <opensmt/Substitutor.h>

// Shall be static - no need to allocate these all the time!
const char* check_opensmt2t::false_str = "false";
const char* check_opensmt2t::true_str = "true";

check_opensmt2t::check_opensmt2t() :
      config(new SMTConfig()),
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
    // This is common to all logics: prop, lra, qfuf, qfcuf
}

void check_opensmt2t::set_random_seed(unsigned int i)
{
    assert(config);
    random_seed = i;
    const char* msg = nullptr;
    config->setOption(SMTConfig::o_random_seed, SMTOption((int)random_seed), msg);
    assert(msg && std::strcmp(msg, "ok") == 0); // The message is set to "ok" if option is set successfully in OpenSMT
}

#ifdef DISABLE_OPTIMIZATIONS 
// Code for init these options
void check_opensmt2t::set_dump_query(bool f)
{
    assert(config);
    const char* msg=nullptr;
    config->setOption(SMTConfig::o_dump_query, SMTOption(f), msg);
    dump_queries = f;
}

void check_opensmt2t::set_dump_query_name(const string& n)
{
    assert(config);
    config->set_dump_query_name(n.c_str());
    base_dump_query_name = n;
    pre_queries_file_name = "__preq_" + base_dump_query_name;
}
#endif

/*******************************************************************\

Function: check_opensmt2t::close_partition

 Purpose: Closes the interpolation partition by passing its CNF form
 (collected in current_partition) to the solver.
This method gathers what has been accumulated in current_partition.
print
std::cout << "\nInsert in top_level_formulas ready to solve:\n" <<logic->pp(pand) <<std::endl;
std::ofstream outFormula ("out_formula.smt2", std::ios::out|std::ios::app);
if(!outFormula.fail()){
    outFormula<<logic->pp(pand) << endl;
    outFormula.close();
}
\*******************************************************************/
void check_opensmt2t::close_partition() {
    assert(!last_partition_closed);
    if (!last_partition_closed) {
#ifdef PARTITIONS_ITP
        std::cout << ";;Closing partition (Count of the created partitions): " << partition_count << '\n';
#endif
        // opensmt can handle special cases like 0 or 1 argument properly
        const PTRef pand = logic->mkAnd(current_partition);
#ifdef PARTITIONS_ITP
        std::cout << ";;Pushing to solver: "<< logic->pp(pand) << '\n' << std::endl;
#endif
        top_level_formulas.push(pand);
        assert((unsigned)top_level_formulas.size() == partition_count);
        current_partition.clear();
        last_partition_closed = true;
#ifdef PARTITIONS_ITP
        if(current_partition.size() == 1){
            std::cout << ";;Trivial partition (terms size = 1): " << partition_count << "\n";
        }
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
            std::cerr << "WARNING: last partition was empty probably due to slicing, or "
            "in UpProver the function signature got changed and summaries would n't match in terms of number of args."
            << std::endl;
        }
        // this is the important statement in this block; before is just checking
        close_partition();
    }
    // we are creating new partition which is not closed at the moment
    last_partition_closed = false;
    return partition_count++;
}

void check_opensmt2t::insert_top_level_formulas() {
#ifdef PARTITIONS_ITP
  std::cout << ";;Inserting formulas to solver from pushed_formulas " << pushed_formulas << " to top_level " << top_level_formulas.size() << std::endl;
#endif
    for(auto i = pushed_formulas; i < (unsigned)top_level_formulas.size(); ++i) {
        char *msg = nullptr;
        mainSolver->insertFormula(top_level_formulas[i], &msg); //in opensmt a new partition gets generated
        if (msg != nullptr) {
            free(msg); // If there is an error, consider print msg
        }
    }
    pushed_formulas = top_level_formulas.size();
}


void check_opensmt2t::produceConfigMatrixInterpolants(const std::vector<std::vector<int> > & configs,
                                                      std::vector<PTRef> & interpolants) const {
    auto itpCtx = mainSolver->getInterpolationContext();

    // First interpolant is true -> all partitions in B
    for ( unsigned i = 0; i < configs.size(); i++ )
    {
        ipartitions_t mask = 0;
        for (unsigned j = 0; j < configs[i].size(); j++)
        {
            setbit ( mask, configs[i][j]);
        }
#ifdef PARTITIONS_ITP
        std::cout << "\n\n;;Mask is " << mask << std::endl;
        std::cout << logic->pp(mainSolver->getPartitionManager().getPartition(mask, PartitionManager::part::A)) << std::endl;
        std::cout << ";;END OF PARTS" <<std::endl;
#endif
        itpCtx->getSingleInterpolant(interpolants, mask);
    }
}

PTRef check_opensmt2t::substitute(PTRef term, Logic::SubstMap const & subst) {
    return Substitutor(*logic, subst).rewrite(term);
}



