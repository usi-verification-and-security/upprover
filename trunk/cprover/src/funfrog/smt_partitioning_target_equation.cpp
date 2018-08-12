/*******************************************************************
 Module: Symex target equation which tracks different partitions for
 different deferred functions. Based on symex_target_equation.cpp.

 Author: Ondrej Sery

 \*******************************************************************/

#include <util/std_expr.h>

#include "smt_partitioning_target_equation.h"

#include "solvers/smtcheck_opensmt2.h"
#include "solvers/smt_itp.h"
#include "partition_iface.h"
#include "utils/naming_helpers.h"
#include "hifrog.h"
#include "summary_store.h"

//#define DEBUG_ITP_SMT // ITP of SMT - testing
//#define DEBUG_ENCODING

#ifdef DISABLE_OPTIMIZATIONS
#include <fstream>
using namespace std;

#include "expr_pretty_print.h"
#endif


bool smt_partitioning_target_equationt::isRoundModelEq(const exprt &expr)
{
    if (!expr.has_operands())
        return false;
    if (expr.operands().size() > 2)
        return false;

    // Start checking if it is auto gen code for rounding model
    std::string str = id2string((expr.operands()[0]).get(ID_identifier));
    if (is_cprover_builtins_var(str))
        return true;
    
    if (expr.operands().size() < 2) return false;
    
    str = id2string((expr.operands()[1]).get(ID_identifier));
    if (is_cprover_builtins_var(str))
        return true;

    return false;
}


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

/*******************************************************************
 Function: smt_partitioning_target_equationt::extract_interpolants

 Inputs:

 Outputs:

 Purpose: Extract interpolants corresponding to the created partitions

 \*******************************************************************/
void smt_partitioning_target_equationt::extract_interpolants(check_opensmt2t& decider) {
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

        if (skip_partition(partition, store_summaries_with_assertion)){
            continue;
        }

        smt_itpt *itp = dynamic_cast <smt_itpt*> (itp_result[tid]);

        tid++;

        if (itp->is_trivial()) {
            std::cout << "Interpolant for function: "
                            << partition.get_iface().function_id.c_str()
                            << " is trivial." << std::endl;
            continue;
        }

        if (partition.get_iface().call_tree_node.is_recursion_nondet()) {
            std::cout << "Skip interpolants for nested recursion calls.\n";
            continue;
        }

        if (itp->is_trivial()) {
            continue;
        }

        auto common_symbs = fill_common_symbols(partition);

#   ifdef DEBUG_ITP_SMT
        std::cout << "Interpolant for function: " <<
        partition.get_iface().function_id.c_str() << std::endl;
        std::cout << "Common symbols (" << common_symbs.size() << "):" << std::endl;
        for (std::vector<symbol_exprt>::iterator it = common_symbs.begin();
                        it != common_symbs.end(); ++it)
            std::cout << it->get_identifier() << std::endl;

        std::cout << "Generalizing interpolant" << std::endl;
#   endif
        std::string fun_name = id2string(partition.get_iface().function_id);
        (static_cast<smtcheck_opensmt2t &>(decider)).generalize_summary(*itp, common_symbs);

        // Store the interpolant; summary_store takes the ownership of the summary pointer itp
        summary_store.insert_summary(itp, fun_name);
    }
#else
    assert(0);
#endif
}

#ifdef DEBUG_SSA_SMT_CALL
// For the case when we have => with cast to bool condition
bool smt_partitioning_target_equationt::isTypeCastConst(const exprt &expr) {
    if (expr.id() != ID_typecast)
        return false;

    if (!expr.has_operands())
        return false;

    if (!(expr.operands())[0].is_constant())
        return false;

    // For LRA only: it will be taken care in the solver or before calling the solver
    if ((expr.operands())[0].is_boolean() ||   // in the solver
            expr.is_boolean())                 // in decider::convert
        return false;

    return true;
}
#else
bool smt_partitioning_target_equationt::isTypeCastConst(const exprt &expr) {
    throw std::logic_error("Should not be called in non-debug setting!");
}
#endif //DEBUG_SSA_SMT_CALL

std::vector<symbol_exprt> smt_partitioning_target_equationt::fill_common_symbols(const partitiont & partition) const {
    // call the base method, which fills the common_symbols according to computed interface of the function
    auto common_symbols = partitioning_target_equationt::fill_common_symbols(partition);

    // MB: In SMT mode, we do not care about CPROVER_rounding mode, that is needed only in PROP mode,
    // we do not want it to leak into the signature of the summary.
    // TODO: Would be nicer if caught earlier, e.g. do not consider it as an accessed global variable in the first place

    // remove CPROVER_rounding_mode symbol from the vector, if it was part of the interface
    common_symbols.erase(std::remove_if(common_symbols.begin(), common_symbols.end(), [](const symbol_exprt& expr){
        return is_cprover_rounding_mode_var(expr);
    }),
    common_symbols.end());
    return common_symbols;
}

