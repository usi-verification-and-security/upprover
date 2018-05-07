
#include "prop_refiner_assertion_sum.h"
#include "partition_iface.h"
#include "prop_partitioning_target_equation.h"
#include "solvers/prop/prop_conv.h"
#include "subst_scenario.h"


/*******************************************************************

 Function: refiner_assertion_sumt::refine

 Inputs:

 Outputs:

 Purpose: Analyses the results of slicing in order to refine,
          Which function call to inline, which to summarize and which to havoc

\*******************************************************************/
void prop_refiner_assertion_sumt::refine(
        const prop_conv_solvert &decider,
        call_tree_nodet &summary,
        prop_partitioning_target_equationt &equation) {
    refined_functions.clear();
    switch (mode) {
        case refinement_modet::FORCE_INLINING:
            reset_inline(summary);
            break;
        case refinement_modet::RANDOM_SUBSTITUTION:
            reset_random(summary);
            break;
        case refinement_modet::SLICING_RESULT:
            reset_depend(decider, summary, equation);
            break;
        default:
            assert(false);
            break;
    }
}

void prop_refiner_assertion_sumt::reset_depend(
        const prop_conv_solvert &decider,
        call_tree_nodet &summary,
        prop_partitioning_target_equationt &equation) {
    std::vector<call_tree_nodet *> tmp;

    partitionst &parts = equation.get_partitions();
    for (unsigned i = 0; i < parts.size(); i++) {
        partitiont part = parts[i];
        if (!part.ignore && (part.summary || part.stub)) {
            partition_ifacet ipart = part.get_iface();
#     ifdef DEBUG_REFINER
            std::cout<< "*** checking " << ipart.function_id << ":" << std::endl;
#     endif
            /*if (part.summary && part.applicable_summaries.empty()) {
      #       ifdef DEBUG_REFINER
              std::cout<< "    -- no applicable summaries" << std::endl;
      #       endif
              tmp.push_back(&ipart.call_tree_node);
            }*/
            if (decider.l_get(ipart.callstart_literal).is_true()) { // in the variant will do prop.lget
#       ifdef DEBUG_REFINER
                std::cout<< "    -- callstart literal is true" << std::endl;
#       endif
                if (ipart.call_tree_node.get_precision() != INLINE) {
                    if (ipart.call_tree_node.is_recursion_nondet()) {
                        status() << "Automatically increasing unwinding bound for "
                                 << ipart.call_tree_node.get_function_id() << eom;
                        omega.refine_recursion_call(ipart.call_tree_node);
                    }
                    set_inline_sum(ipart.call_tree_node);
                }
            }
        }
    }
}
