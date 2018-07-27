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
    assert(!current_partition.empty());
    if (partition_count > 0 && !current_partition.empty()) {
        const PTRef pand = current_partition.size() > 1 ?
                           logic->mkAnd(current_partition) : (current_partition)[0];
        top_level_formulas.push(pand);
        assert(top_level_formulas.size() == partition_count);
#ifdef DEBUG_SMT2SOLVER
        if(current_partition->size() == 1){
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
//Allowing partitions for havoced functions and fully slices ones

    assert(partition_count == 0 || !current_partition.empty());
    if (partition_count != 0 && current_partition.empty()) {
        std::cerr << "WARNING: last partition was empty (probably due to slicing)." << std::endl;
// NOTE: The index is reused for the next partition, outer context must
// ensure that the previously returned index is not used.
        partition_count--;
    }

// Finish the previous partition if any
    if (!current_partition.empty()) {
        close_partition();
        current_partition.clear();
    }
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
#ifdef DISABLE_OPTIMIZATIONS
        if (dump_pre_queries)
        {
            out_smt << "; XXX Partition: " << (top_level_formulas.size() - i - 1) << endl;
            char* s = logic->printTerm(top_level_formulas[i]);
            out_smt << "(assert \n" << s << "\n)\n";
            free(s);
        }
#endif
    }
    pushed_formulas = top_level_formulas.size();
}

