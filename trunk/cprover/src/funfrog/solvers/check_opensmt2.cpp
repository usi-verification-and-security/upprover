//
// Created by Martin Blicha on 27.07.18.
//

#include "check_opensmt2.h"



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
        assert(top_level_formulas.size() == partition_count);
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
    for(auto i = pushed_formulas; i < top_level_formulas.size(); ++i) {
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

