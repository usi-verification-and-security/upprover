/*******************************************************************

 Module: Refining schema for function summarization.
         Supposed to have different implementations.

 Author: Grigory Fedyukovich

\*******************************************************************/


#include "refiner_assertion_sum.h"

#include "subst_scenario.h"
#include "summary_store.h"
#include "partitioning_target_equation.h"
#include "partition_iface.h"
#include "funfrog/interface/solver/solver.h"

void refiner_assertion_sumt::set_inline_sum(call_tree_nodet& node)
{
  std::string function_name = id2string(node.get_function_id());
  if (node.get_call_location() <= last_assertion_loc){
    status() << (std::string("*** REFINING function: ") + function_name) << eom;
    node.set_inline();
    refined_functions.push_back(&node);
  }
}

void refiner_assertion_sumt::reset_inline(call_tree_nodet& node)
{
  for (call_sitest::iterator it = node.get_call_sites().begin();
          it != node.get_call_sites().end(); ++it)
  {
    if ((it->second).get_precision() != INLINE){
      set_inline_sum(it->second);
      if ((it->second).is_recursion_nondet()){
          status() << "Automatically increasing unwinding bound for " << (it->second).get_function_id() << eom;
          omega.refine_recursion_call(it->second);
      }
    }
    else {
      reset_inline(it->second);
    }
  }
}

void refiner_assertion_sumt::reset_random(call_tree_nodet& node)
{
  unsigned summs_size = omega.get_summaries_count();
    for (call_sitest::iterator it = node.get_call_sites().begin();
            it != node.get_call_sites().end(); ++it)
    {
      summary_precisiont precision = (it->second).get_precision();
      if ((precision == SUMMARY) ||    // if there were some summaries,
                                       // try to inline them first
          (precision == HAVOC && summs_size == 0)){  // and if there were not
                                                     // then refine havoced calls
        if (rand() % 1000 < 300 || rand() % 1000 > 800){
          set_inline_sum(it->second);
        }
      }
      reset_random(it->second);
                                       // TODO: we can actually try do it vice-versa
    }                                  // but due to more sophisticated choice of nondets in s_info init
                                       // there are more chances that the reason of SAT was in 2weak summaries
}

/*******************************************************************
 Purpose: Analyses the results of slicing in order to refine,
          Which function call to inline, which to summarize and which to havoc

\*******************************************************************/
void refiner_assertion_sumt::mark_sum_for_refine(
        const solvert &solvert,
        call_tree_nodet &treeNode,
        partitioning_target_equationt &equation) {
    refined_functions.clear();
    switch (mode) {
        case refinement_modet::FORCE_INLINING:
            reset_inline(treeNode);
            break;
        case refinement_modet::RANDOM_SUBSTITUTION:
            reset_random(treeNode);
            break;
        case refinement_modet::SLICING_RESULT:       //Default
            reset_inline_with_opt(solvert, treeNode, equation); //set node as inline if has sum & ...
            break;
        default:
            assert(false);
            break;
    }
}

void refiner_assertion_sumt::reset_inline_with_opt(
        const solvert &solver,
        call_tree_nodet &treeNode,
        partitioning_target_equationt &equation) {
    std::vector<call_tree_nodet *> tmp;

    partitionst & parts = equation.get_partitions();
    for (unsigned i = 0; i < parts.size(); i++) {
        partitiont part = parts[i];
        if (!part.ignore && (part.has_abstract_representation())) {
            partition_ifacet ipart = part.get_iface();
            //std::cout<< "*** checking " << ipart.function_id << ":" << std::endl;
            //filter out function calls which do not affect satisfiability of the assertion.
            // e.g: fun(); int x =0; assert(x>=0); no need to inline fun() as it does n't matter
            if (solver.is_assignment_true(ipart.callstart_literal)) {
                //std::cout<< "    -- callstart literal is true" << std::endl;
                //Grisha's paper 2014 for the summarization-based automatic detection of recursion depth
                if (ipart.call_tree_node.get_precision() != INLINE) {
                    if (ipart.call_tree_node.is_recursion_nondet()) {
                        status() << "Automatically increasing unwinding bound for "
                                 << ipart.call_tree_node.get_function_id() << eom;
                        //unwind the calltree on demand
                        omega.refine_recursion_call(ipart.call_tree_node);
                    }
                    set_inline_sum(ipart.call_tree_node); //main action set node as inline
                }
            }
        }
    }
}

