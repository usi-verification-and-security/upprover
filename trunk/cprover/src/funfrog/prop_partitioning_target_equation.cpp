
/*******************************************************************\

Module: Symex target equation which tracks different partitions for
different deferred functions. Based on symex_target_equation.cpp.

Author: Ondrej Sery

\*******************************************************************/

#include <util/std_expr.h>

#include "prop_partitioning_target_equation.h"
#include "solvers/sat/cnf.h"
#include "solvers/satcheck_opensmt2.h"
#include "utils/naming_helpers.h"
#include "partition_iface.h"
#include "solvers/prop_itp.h"
#include "summary_store.h"


//#define DEBUG_ITP // ITP of SAT - testing

#ifdef DISABLE_OPTIMIZATIONS
#include <fstream>
using namespace std;

#include "expr_pretty_print.h"
#include "hifrog.h"
#endif


#ifdef PRODUCE_PROOF
namespace{
  // helper methods for extract_interpolants

  // MB: we are skipping main and __CPROVER_initialize because it is pointless to compute interpolants for these partitions
  // and these methods are special with respect to the globals (see function_infot::analyze_globals_rec)
  // which broke the computation of interpolant for __CPROVER_initialize
  bool skip_partition_with_name(const std::string & name){
    return is_cprover_initialize_method(name) || is_main(name);
  }

  bool skip_partition(partitiont & partition, bool store_summaries_with_assertion){
      return !partition.is_real_ssa_partition() ||
             (partition.get_iface().assertion_in_subtree && !store_summaries_with_assertion) ||
             partition.get_iface().call_tree_node.is_recursion_nondet() ||
             skip_partition_with_name(partition.get_iface().function_id.c_str());
  }
}
#endif // PRODUCE_PROOF

/*******************************************************************\

Function: prop_partitioning_target_equationt::extract_interpolants

  Inputs:

 Outputs:

 Purpose: Extract interpolants corresponding to the created partitions

\*******************************************************************/
void prop_partitioning_target_equationt::extract_interpolants(check_opensmt2t& decider)
{
#ifdef PRODUCE_PROOF     
  // Prepare the interpolation task. NOTE: ignore the root partition!
  unsigned valid_tasks = 0;

  // Clear the used summaries
  for (unsigned i = 0; i < partitions.size(); ++i)
    partitions[i].get_iface().call_tree_node.clear_used_summaries();

  // Find partitions suitable for summary extraction
  for (unsigned i = 1; i < partitions.size(); ++i) {
    partitiont& partition = partitions[i];

      // Mark the used summaries
      if (partition.has_summary_representation() && !(partition.ignore)) {
          for (auto summary_id : partition.applicable_summaries) {
              partition.get_iface().call_tree_node.add_used_summary(summary_id);
          }
      }
    
    if (!skip_partition(partition, store_summaries_with_assertion)){
      valid_tasks++;
    }
  }
  
  // Only do the interpolation if there are some interpolation tasks
  if (valid_tasks == 0)
    return;

  interpolation_taskt itp_task(valid_tasks);

  for (unsigned pid = 1, tid = 0; pid < partitions.size(); ++pid) {
    partitiont& partition = partitions[pid];

    if (!skip_partition(partition, store_summaries_with_assertion)){
      fill_partition_ids(pid, itp_task[tid++]);
    }
  }

  // Interpolate...
  interpolantst itp_result;
  itp_result.reserve(valid_tasks);
  decider.get_interpolant(itp_task, itp_result);

  // Interpret the result
  for (unsigned pid = 1, tid = 0; pid < partitions.size(); ++pid) {
    partitiont& partition = partitions[pid];

    if (skip_partition(partition, store_summaries_with_assertion)) {
      continue;
    }

    prop_itpt* itp = dynamic_cast <prop_itpt*> (itp_result[tid]);

    tid++;

    if (itp->is_trivial()) {
      std::cout << "Interpolant for function: " <<
                partition.get_iface().function_id.c_str() << " is trivial." << std::endl;
      continue;
    }

    if (partition.get_iface().call_tree_node.is_recursion_nondet()){
      std::cout << "Skip interpolants for nested recursion calls." << std::endl;
      continue;
    }

    // Generalize the interpolant
    auto common_symbs = fill_common_symbols(partition);

#   ifdef DEBUG_ITP
    std::cout << "Interpolant for function: " <<
            partition.get_iface().function_id.c_str() << std::endl;
    std::cout << "Common symbols (" << common_symbs.size() << "):" << std::endl;
    for (std::vector<symbol_exprt>::iterator it = common_symbs.begin();
            it != common_symbs.end(); ++it)
      std::cout << it->get_identifier() << std::endl;

    std::cout << "Generalizing interpolant" << std::endl;
#   endif
      dynamic_cast<satcheck_opensmt2t&>(decider).generalize_summary(*itp, common_symbs);

    if (itp->is_trivial()) {
      continue;
    }

    // Store the interpolant
    summary_store.insert_summary(itp, id2string(partition.get_iface().function_id));

  }
  
#else
  assert(0);
#endif
}
