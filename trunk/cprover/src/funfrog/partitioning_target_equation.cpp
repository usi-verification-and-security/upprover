/*******************************************************************
 Module: Symex target equation which tracks different partitions for
 different deferred functions. Based on symex_target_equation.cpp.

 \*******************************************************************/

#include "partitioning_target_equation.h"
#include "partition_iface.h"
#include "call_tree_node.h"
#include "utils/naming_helpers.h"
#include "summary_store.h"
#include "conversion_utils.h"
#include "interface/solver/interpolating_solver.h"

#include <numeric>
#include <algorithm>
#include <iostream>

#ifdef DISABLE_OPTIMIZATIONS
#include <fstream>
#endif //DISABLE_OPTIMIZATIONS

using namespace hifrog;

partitioning_target_equationt::partitioning_target_equationt(
  const namespacet & _ns,
  summary_storet & summary_store,
  bool _store_summaries_with_assertion, message_handlert & message_handler) :
  symex_target_equationt(message_handler),
  current_partition_id(NO_PARTITION_ID),
#         ifdef DISABLE_OPTIMIZATIONS
    dump_SSA_tree(false),
    ssa_tree_file_name("__ssa_tree.smt2"),
    terms_counter(0),
    is_first_call(true),
    first_call_expr(0),
#endif
  io_count_global(0),
  summary_store{summary_store},
  store_summaries_with_assertion(_store_summaries_with_assertion)    //initializes boolean flag in all-claims with "true", otherwise false
  {
#ifdef DISABLE_OPTIMIZATIONS
    partition_smt_decl = new std::map <std::string,exprt>();
#endif
}

/*******************************************************************
 Function: partitioning_target_equationt::reserve_partition

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/
partition_idt partitioning_target_equationt::reserve_partition(partition_ifacet& partition_iface)
{
    partition_idt new_id = partitions.size();
    partition_idt parent_id = partition_iface.parent_id;

    partitions.push_back(partitiont(parent_id, partition_iface));

    bool check = partition_map.insert(partition_mapt::value_type(
            partition_iface.callend_symbol.get_identifier(), new_id)).second;
    assert(check);
    (void)check;

    if (parent_id != NO_PARTITION_ID) {
        partitions[parent_id].add_child_partition(new_id, partition_iface.call_loc);
    }
    partition_iface.partition_id = new_id;

    return new_id;
}

void partitioning_target_equationt::refine_partition(partition_idt partition_id)
{
    partitiont& partition = partitions[partition_id];
    if (partition.get_iface().call_tree_node.node_has_summary()) {
        if (!partition.has_abstract_representation()) {
            throw std::logic_error{"Trying to refine a partition that was not summarized or stubbed before!"};
        }
        partition.remove_abstract_representation();
        //partition.partition_summary_ID_vec.clear();
        //partition.partition_summary_ID_set.clear();
        partition.partition_summaryID = 0;
    }
}


/*******************************************************************

 Purpose: SA: usage only in HiFrog

 \*******************************************************************/
//void partitioning_target_equationt::fill_summary_partition(partition_idt partition_id, const std::string & function_id)
//{
//    assert(summary_store.has_summaries(function_id));
//    if(!summary_store.has_summaries(function_id)){
//        throw std::logic_error{"Trying to set non-existent summary_ids_vec to a partition for " + function_id};
//    }
//    std::cout << "##fill summary for fname: " <<function_id<<" ";
//    auto const & summary_ids_vec = summary_store.get_summariesID(function_id);
//    assert(!summary_ids_vec.empty());
//
//    partitiont& sum_partition = partitions.at(partition_id);
//    std::cout << ", with partition_ID summary: " <<partition_id<<" ";
//
//    sum_partition.add_summary_representation();
//    sum_partition.partition_summary_ID_vec = summary_ids_vec;
//
//    sum_partition.partition_summary_ID_set.clear();
//    //copy summary_ids_vec into node_summaryID_set
//    for (unsigned long summary_id : summary_ids_vec) {
//        sum_partition.partition_summary_ID_set.insert(summary_id);
//        std::cout << "with summary ID of : " <<summary_id<<"\n";
//    }
//}

/*******************************************************************

 Purpose: usage only in UpProver
Note: obtain summary ID from node.
 customized for UpProver to work with single sumID
 \*******************************************************************/
void partitioning_target_equationt::fill_summary_partition(partition_idt partition_id, call_tree_nodet & node)
{
    if(!node.node_has_summary()){
        std::string fname = node.get_function_id().c_str(); //cast char* to string
        throw std::logic_error{"Trying to set non-existent summary_id to a partition for " + fname};
    }
    //always get sumID from node (one-to-one mapping), not function name (NO one-to-one mapping)!
    const summary_idt & sum_ID = node.get_node_sumID();
    partitiont& sum_partition = partitions.at(partition_id);
    
#ifdef PRINT_DEBUG_UPPROVER
    std::cout << "@@fill summary for partition_id: " <<partition_id <<" , with sum_ID: " <<sum_ID<<"\n";
#endif
    sum_partition.add_summary_representation();

    sum_partition.partition_summaryID = sum_ID;
}

/*******************************************************************
 Purpose: Collects information about the specified partitions for later
 processing and conversion

 \*******************************************************************/

void partitioning_target_equationt::prepare_partitions() { // for hifrog only
    // Fill in the partition start and end iterator for easier access during
    // the conversion process
    unsigned idx = 0;
    SSA_stepst::iterator ssa_it = SSA_steps.begin();

    // The last partition has an undefined end, fix it!
    close_current_partition();

    // we need to process the partitions in the order as they appear in SSA_steps
    const auto & const_partitions = this->partitions;
    std::vector<std::size_t> indices(partitions.size());
    std::iota(indices.begin(), indices.end(), 0);
    auto unprocessed_it = std::partition(indices.begin(), indices.end(),
                                         [&const_partitions](std::size_t idx){return const_partitions[idx].has_ssa_representation();});
    std::sort(indices.begin(), unprocessed_it, [&const_partitions](std::size_t i1, std::size_t i2){
        return const_partitions[i1].start_idx < const_partitions[i2].start_idx;
    });

    for (auto it = indices.begin(); it != unprocessed_it; ++it) {
        auto & partition = partitions[*it];
        assert(idx == partition.start_idx);
        bool ignore = true;

        partition.start_it = ssa_it;

        while (idx != partition.end_idx) {
            assert(ssa_it != SSA_steps.end());
            ignore &= ssa_it->ignore;
            ++ssa_it;
            ++idx;
        }
        partition.end_it = ssa_it;
        partition.ignore = ignore & !partition.get_iface().assertion_in_subtree;
    }
}

/*******************************************************************
 Function: partitioning_target_equationt::prepare_SSA_exec_order

 Inputs:

 Outputs:

 Purpose: Fills in the SSA_steps_exec_order holding pointers to SSA steps 
 ordered in the order of program execution (i.e., as they would be normally 
 ordered in symex_target_equation).
//also is used for building error trace
 \*******************************************************************/
void partitioning_target_equationt::prepare_SSA_exec_order(
		const partitiont& partition) {
    partition_locst::const_iterator loc_it = partition.child_locs.begin();
    partition_idst::const_iterator id_it = partition.child_ids.begin();
    unsigned SSA_idx = partition.start_idx;

    for (SSA_stepst::iterator it = partition.start_it; 
        it != partition.end_it; ++it, ++SSA_idx) {
        while (loc_it != partition.child_locs.end() && *loc_it == SSA_idx) {
            // Process the call first
            const partitiont& partition = partitions[*id_it];

            if (partition.is_real_ssa_partition())
                prepare_SSA_exec_order(partition);

            ++loc_it;
            ++id_it;
        }
        // Add current step
        SSA_steps_exec_order.push_back(&*it);
    }
    while (loc_it != partition.child_locs.end() && *loc_it == SSA_idx) {
        // Process the call first
        const partitiont& partition = partitions[*id_it];

        if (partition.is_real_ssa_partition())
            prepare_SSA_exec_order(partition);

        ++loc_it;
        ++id_it;
    }
}

/*******************************************************************
 Function: partitioning_target_equationt::find_target_partition

 Inputs:

 Outputs:

 Purpose: Find partition corresponding to the function call. 
 If the given SSA step is a callend assumption, the corresponding target 
 partition is returned. If not, NULL is returned.

 \*******************************************************************/
const partitiont* partitioning_target_equationt::find_target_partition(
		const SSA_stept& step) {
    if (step.cond_expr.id() == ID_symbol || (step.cond_expr.id() == ID_implies
                    && step.cond_expr.op1().id() == ID_symbol)) {
        irep_idt id = step.cond_expr.id() == ID_symbol ? step.cond_expr.get(
                        ID_identifier) : step.cond_expr.op1().get(ID_identifier);
        partition_mapt::iterator pit = partition_map.find(id);
        if (pit != partition_map.end()) {
            return &partitions[pit->second];
        }
    }
    return nullptr;
}

/*******************************************************************
 Function: partitioning_target_equationt::fill_partition_ids

 Inputs:

 Outputs:

 Purpose: Fill in ids of all the child partitions in the subtree
This is required to create the A-part of interpolation problem
 \*******************************************************************/
void partitioning_target_equationt::fill_partition_ids(
		partition_idt partition_id, fle_part_idst& part_ids) {

    partitiont& partition = partitions[partition_id];
    if (partition.is_stub()) {
        return;
    }
    assert( (!partition.get_iface().assertion_in_subtree || store_summaries_with_assertion));
    if (partition.ignore) {
        assert(partition.child_ids.empty());
        return;
    }
    assert(partition.is_real_ssa_partition() || partition.child_ids.empty());

    // Current partition id
    for(auto curr_id : partition.get_fle_part_ids()){
        part_ids.push_back(curr_id);
    }

    // Child partition ids
    for (auto child_id : partition.child_ids) {
        fill_partition_ids(child_id, part_ids); //recursive call
    }
}

void partitioning_target_equationt::fill_stub_partition(partition_idt partition_id) {
    partitiont & partition = partitions.at(partition_id);
    assert(partition.has_no_representation());
    partition.add_stub_representation();
}

void partitioning_target_equationt::select_partition(partition_idt partition_id) {
    close_current_partition();
    // Select the new partition
    current_partition_id = partition_id;
    partitiont & new_partition = get_current_partition();
    assert(!new_partition.has_ssa_representation());
    if(new_partition.has_ssa_representation()){
        throw std::logic_error("About to process partition that has been processed already!");
    }
    new_partition.start_idx = SSA_steps.size();
}



unsigned partitioning_target_equationt::count_partition_assertions(const partitiont & partition) const {
    unsigned i = 0;
    for (SSA_stepst::const_iterator
           it = partition.start_it;
         it != partition.end_it; it++)
        if (it->is_assert()) i++;
    return i;
}

void partitioning_target_equationt::close_current_partition()  {
    if (current_partition_id != NO_PARTITION_ID) {
        auto & partition = get_current_partition();
        partition.end_idx = SSA_steps.size();
        assert(!partition.has_ssa_representation());
        partition.add_ssa_representation();
        current_partition_id = NO_PARTITION_ID;
    }
}

/***************************************************************************/
#ifdef DISABLE_OPTIMIZATIONS
std::ostream& partitioning_target_equationt::print_decl_smt(std::ostream& out) {
    if (!partition_smt_decl->empty())
    {
        // Print all decl
        for (std::map<std::string, exprt>::iterator it =
                        partition_smt_decl->begin(); it != partition_smt_decl->end(); ++it) {
                out << "(declare-fun " << it->first << ")" << std::endl;
        }

        // At the end of the loop
        partition_smt_decl->clear(); //Ready for the next partition
    }
    return out;
}

void partitioning_target_equationt::print_partition() {
    // When creating the real formula - do not add the assert here, check first if OpenSMT2 does it
    std::string basic_str = out_basic.str();
    out_partition << "; " << basic_str;
    std::string terms_str = out_terms.str();
    if (terms_str.length() > 0) {
        out_partition << "(assert\n";
        if (terms_counter > 1)
            out_partition << "  (and\n" << terms_str << "  )\n)" << '\n';
        else
            out_partition << terms_str << ")" << '\n';
    }

    // Init for reuse
    out_terms.str("");
    out_terms.clear();
    out_basic.str("");
    out_basic.clear();
    terms_counter = 0;
}
//print SSA forms into file __SSA_query_default_1.smt2
#ifdef DISABLE_OPTIMIZATIONS
void partitioning_target_equationt::print_all_partition(std::ostream& out) {
    // Print only if the flag is on!
    // Print header - not part of temp debug print!
    out << "\nXXX SSA --> SMT-lib Translation XXX\n";

    // for prints later on
    std::ostream out_decl(0);
    std::stringbuf decl_buf;
    out_decl.rdbuf(&decl_buf);

    // When creating the real formula - do not add the assert here, check first if OpenSMT2 does it
    print_decl_smt(out_decl); // print the symbol decl
    // print each partition
    out << decl_buf.str() << out_partition.str() << "(check-sat)\n";
}
#endif
void partitioning_target_equationt::getFirstCallExpr() 
{
//    saveFirstCallExpr(partitions.at(1).get_iface().callstart_symbol);
}

void partitioning_target_equationt::saveFirstCallExpr(const exprt& expr) {
    if (!is_first_call)
        return;
    
    is_first_call = false;
    first_call_expr = &expr;
}

bool partitioning_target_equationt::isFirstCallExpr(const exprt& expr) {
    if (is_first_call)
        return false;

    //return (first_call_expr->compare(expr) != 0); // for debug
    return (first_call_expr->pretty().compare(expr.pretty()) != 0);
}
#endif

/*******************************************************************
 Function: partitioning_target_equationt::convert_partition_assertions

 Purpose: Convert a specific partition assertions of SSA steps

 \*******************************************************************/

void partitioning_target_equationt::convert_partition_assertions(
        convertort &convertor, partitiont &partition)
{
    unsigned number_of_assumptions = 0;
    const partition_ifacet& partition_iface = partition.get_iface();

    std::vector<FlaRef> error_lits;

    exprt assumption_expr = true_exprt();
    auto var_constraints_lit = convertor.get_and_clear_var_constraints(); //boundaries for LA
    for (symex_target_equationt::SSA_stepst::iterator it = partition.start_it; it != partition.end_it; ++it) {
        if(it->ignore) {continue;} // ignored instructions can be skippied
        if (it->is_assert()) {

            // Collect ass \in assertions(f) in bv
            FlaRef tmp_literal = convertor.land(convertor.convert_bool_expr(it->cond_expr), var_constraints_lit);
//          it->cond_literal = flaref_to_literal(convertor.limplies(assumption_literal, tmp_literal));
//          Commented since CProver5.12: Instead of converting to Literalt, use CProver methods operating on exprt to exprt
            it->cond_handle = implies_exprt(assumption_expr, it->cond_expr);
//          error_lits.push_back(!literal_to_flaref(it->cond_literal)); // negated literal
            error_lits.push_back(!convertor.limplies(convertor.convert_bool_expr(assumption_expr), tmp_literal)); // negated literal
    
        } else if (it->is_assume()) {
            // If the assumption represents a call of the function g,
            // encode callstart_g propagation formula:
            //
            // callstart_g <=>
            //     path_cond \land
            //     (\land_{ass \in {assumptions(f)}} ass)
            //
            const partitiont* target_partition = find_target_partition(*it);

            if (target_partition && !target_partition->ignore) {
                const partition_ifacet& target_partition_iface =
                        target_partition->get_iface();
    
//              FlaRef tmp = convertor.land(assumption_literal,literal_to_flaref(it->guard_literal));
                FlaRef tmp = convertor.land(convertor.convert_bool_expr(assumption_expr), convertor.convert_bool_expr(it->guard_handle));
    
                convertor.set_equal(tmp, target_partition_iface.callstart_literal);

#		ifdef DISABLE_OPTIMIZATIONS
                //out_terms << "XXX Call START equality: \n";
                    terms_counter++;
                    int assume_counter = 0;
                    expr_ssa_print(out_terms << "    (= ",
                        target_partition_iface.callstart_symbol, partition_smt_decl, false);

                    std::stringstream out_temp;
                    for (auto it2 = partition.start_it; it2 != it; ++it2) {
                        if (it2->is_assume() && !it2->ignore) {
                            assume_counter++;
                            expr_ssa_print(out_temp << "        ", it2->cond_expr, partition_smt_decl, false);
                        }
                    }
                    // If there are more than one term - add and
                    switch (assume_counter) {
                    case 0:
                        out_terms << out_temp.str() << "        true\n" << "    )\n";
                        break; // Shall be called only once at the beginning of the code
                    case 1:
                        out_terms << out_temp.str() << "    )\n";
                        break;
                    default:
                        out_terms << "      (and \n" << out_temp.str() << "      )\n" << "    )\n";
                        break;
                    }
#               endif
            }

            // Collect this assumption as:
            //assumption_literal = \land_{ass \in assumptions(f)} ass
            //Commented since CProver5.12: Instead of converting to Literalt, use CProver methods operating from exprt to exprt
            //assumption_literal = convertor.land(assumption_literal, literal_to_flaref(it->cond_literal));
            assumption_expr = and_exprt(assumption_expr, it->cond_handle);
            number_of_assumptions++;
        }
    }

    for (auto const & child_id : partition.child_ids) {
        const partitiont& target_partition = partitions[child_id];
        if (target_partition.get_iface().assertion_in_subtree) {
            // Collect error_g, where g \in children(f) in bv
            error_lits.push_back(target_partition.get_iface().error_literal);
        }
    }

    // Encode the collected assertions:
    //
    // error_f <=>
    //     (\lor_{g \in children(f)} error_g) \lor
    //     (\lor_{ass \in assertions(f)} ass)
    //
    if (!error_lits.empty()) {
        assert(partition_iface.assertion_in_subtree);
        convertor.set_equal(convertor.lor(error_lits), partition_iface.error_literal);
        if (!partition.has_parent()) {
            convertor.assert_literal(partition_iface.error_literal);
        }
    }

//    if (partition.has_parent()) {
        // MB: This relation, that if the function ends then all its assumptions have been satisfied should always be
        //      captured. We need it in UpProver when we are doing symex on subtrees of the program.
        assert(!partition.has_parent() || number_of_assumptions > 0);
        // Encode callend propagation formula for the partition:
        //
        // callend_f =>
        //     (\land_{ass \in assumptions(f)} ass)
        //
        // NOTE: callstart_f \in assumptions(f)
        //

        auto tmp = convertor.limplies(partition_iface.callend_literal, convertor.convert_bool_expr(assumption_expr));
        convertor.assert_literal(tmp);

#       ifdef DISABLE_OPTIMIZATIONS
        //out_terms << "XXX Call END implication: \n";
        terms_counter++;
        expr_ssa_print(out_terms << "    (=> ", partition_iface.callend_symbol,
                        partition_smt_decl, false, true);
        std::stringstream out_temp; // Pre-order printing
        int assume_counter = 0;
        for (auto it2 = partition.start_it; it2 != partition.end_it; ++it2) {
            if (it2->is_assume() && !it2->ignore) {
                if (assume_counter == 0 && isFirstCallExpr(it2->cond_expr)) {
                    assume_counter++;
                    expr_ssa_print(out_temp << "        ", it2->guard,
                                    partition_smt_decl, false);
                }
                assume_counter++;
                expr_ssa_print(out_temp << "        ", it2->cond_expr,
                                partition_smt_decl, false);
            }
        }
        if (assume_counter > 1)
            out_terms << "\n      (and \n" << out_temp.str() << "      )\n" << "    )\n";
        else
            out_terms << "\n" << out_temp.str() << "    )\n";
#   endif
//    }
}

/*******************************************************************
 Function: partitioning_target_equationt::convert_partition_assumptions

 Purpose: Convert a specific partition assumptions of SSA steps

 \*******************************************************************/

void partitioning_target_equationt::convert_partition_assumptions(
        convertort &convertor, partitiont &partition) {
    for (symex_target_equationt::SSA_stepst::iterator it = partition.start_it; it != partition.end_it; ++it) {
        if (it->is_assume()) {
            //it->cond_literal = flaref_to_literal(it->ignore ? const_formula(true) : convertor.convert_bool_expr(it->cond_expr));
            it->cond_handle = it->ignore ? true_exprt() : (it->cond_expr);
        }
    }
}

/*******************************************************************
 Function: partitioning_target_equationt::convert_partition_io

 Inputs:

 Outputs:

 Purpose: Convert a specific partition io of SSA steps

 \*******************************************************************/

void partitioning_target_equationt::convert_partition_io(
        convertort &convertor, partitiont &partition) {
    for (SSA_stepst::iterator it = partition.start_it; it != partition.end_it; ++it) {
        if (!it->ignore) {
            for (std::list<exprt>::const_iterator o_it = it->io_args.begin(); o_it
                                                                              != it->io_args.end(); ++o_it) {
                exprt tmp = *o_it;
                if (tmp.is_constant() || tmp.id() == ID_string_constant)
                    it->converted_io_args.push_back(tmp);
                else {
                    symbol_exprt symbol((CProverStringConstants::IO_CONST + std::to_string(io_count_global++)),
                                        tmp.type());
                    convertor.set_to_true(equal_exprt(tmp, symbol));
                    it->converted_io_args.push_back(symbol);
                }
            }
        }
    }
}

/*******************************************************************
 Function: partitioning_target_equationt::convert_partition_summary

 Purpose: Convert a summary partition (i.e., assert its summary)
Note: SA: customized for UpProver to work with single sumID
 \*******************************************************************/

void partitioning_target_equationt::convert_partition_summary(
        interpolating_solvert &interpolator, partitiont &partition)
{
    auto common_symbs = partition.get_iface().get_iface_symbols();
    //unsigned i = 0;

    bool is_recursive = partition.get_iface().call_tree_node.is_recursive(); //on_nondet();
    //unsigned last_summary = partition.partition_summary_ID_set.size() - 1;

//    for (auto summary_id : partition.partition_summary_ID_set)
//    {
//        if (partition.get_iface().call_tree_node.get_node_sumID() != 0) {
//            auto &summary = summary_store.find_summary(summary_id);
//            if ((!is_recursive || last_summary == i++)) {
//                // we do not want to actually change the summary, because we might need the template later,
//                // we just get a PTRef to the substituted version
//                interpolator.insert_substituted(summary, common_symbs);
//            }
//        }
//    }
    //there is at most one summary per partition
    if (partition.get_iface().call_tree_node.node_has_summary()) {
        summary_idt summary_id = partition.get_iface().call_tree_node.get_node_sumID();
        auto &summary = summary_store.find_summary(summary_id);
        if ((!is_recursive)) {
            // we do not want to actually change the summary, because we might need the template later,
            // we just get a PTRef to the substituted version
            interpolator.insert_substituted(summary, common_symbs);
        }
    }
    
}

/*******************************************************************
 Function: partitioning_target_equationt::convert_partition
ll
 Inputs:

 Outputs:

 Purpose: Convert a specific partition of SSA steps

 \*******************************************************************/
void partitioning_target_equationt::convert_partition(
        convertort &convertor, interpolating_solvert &interpolator,
        partitiont &partition) {
    if (partition.ignore) {
        return;
    }
    // Convert the assumption propagation symbols
    partition_ifacet &partition_iface = partition.get_iface();
    partition_iface.callstart_literal = convertor.convert_bool_expr(
            partition_iface.callstart_symbol);
    partition_iface.callend_literal = convertor.convert_bool_expr(
            partition_iface.callend_symbol);
    if (partition_iface.assertion_in_subtree) {
        partition_iface.error_literal = convertor.convert_bool_expr(partition_iface.error_symbol);
    }
    if (partition.is_stub()) {
        return;
    }

    // Tell the interpolator about the new partition.
    partition.add_fle_part_id(interpolator.new_partition());

    // If this is a summary partition, apply the summary
    if (partition.has_summary_representation() && !(partition.ignore) && partition.get_iface().call_tree_node.node_has_summary()) {
        convert_partition_summary(interpolator, partition);
        return;
    }
    // Convert the corresponding SSA steps

    convert_partition_guards(convertor, partition);
    convert_partition_assignments(convertor, partition);
    convert_partition_assumptions(convertor, partition);
    convert_partition_assertions(convertor, partition);
    convert_partition_io(convertor, partition);
}

/*******************************************************************/

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
        return !partition.is_real_ssa_partition() || //i.e. has abstract repr
               (partition.get_iface().assertion_in_subtree && !store_summaries_with_assertion) || //if there is assertion in subtree of a function, we dont generate summary for that function
               // since the err symbol would appear in the summary interface and would get wierd
               partition.get_iface().call_tree_node.is_recursion_nondet() ||
               skip_partition_with_name(partition.get_iface().function_id.c_str());
    }
}
#endif // PRODUCE_PROOF

/*******************************************************************
 Function: partitioning_target_equationt::convert

 Inputs:

 Outputs:

 Purpose: Convert all the SSA steps into the corresponding formulas in
 the corresponding partitions

 \*******************************************************************/
void partitioning_target_equationt::convert(convertort &convertor,
                                            interpolating_solvert &interpolator) {
#ifdef DISABLE_OPTIMIZATIONS
    getFirstCallExpr(); // Save the first call to the first function
#endif
    for (auto it = partitions.rbegin(); it != partitions.rend(); ++it) {
        convert_partition(convertor, interpolator, *it);
#   ifdef DISABLE_OPTIMIZATIONS
        if (it->get_fle_part_ids().empty()) { continue;} // NO conversion happend
        out_basic << "XXX Partition: " << it->get_fle_part_ids().back() << " (ass_in_subtree: "
                  << it->get_iface().assertion_in_subtree << ")" << " - "
                  << it->get_iface().function_id.c_str() << " (loc: "
                  << it->get_iface().call_tree_node.get_call_location() << ", "
                  << ((it->has_summary_representation()) ?  "SUM"
                                    : ((it->is_stub()) ? "STUB" : "INL")) << ")" << std::endl;

        print_partition();
#   endif
    }

#ifdef DISABLE_OPTIMIZATIONS
    if (dump_SSA_tree)
      {
        std::ofstream out_ssaT;
        out_ssaT.open(ssa_tree_file_name+"_"+std::to_string(get_unique_index())+".smt2");

        // Print all after the headers: decl and code
        print_all_partition(out_ssaT);

        out_ssaT.close();
      }
#endif
}
/*******************************************************************
 Function: partitioning_target_equationt::extract_interpolants()

 Inputs:

 Outputs:

 Purpose: Extract interpolants corresponding to the created partitions
SA: inner method- called by extract_interpolants from core_checker;
 this method covers the required functionality for UpProver
 \*******************************************************************/
void partitioning_target_equationt::extract_interpolants(interpolating_solvert &interpolator) {
#ifdef PRODUCE_PROOF
    // Prepare the interpolation task. NOTE: ignore the root partition!
    //number of interpolation task after UNSAT proof
    unsigned valid_tasks = 0;

//Clear the node_summaryID_set //SA:doesn't clear node_summaryID_set!
//    for (auto const & partition : partitions){
//        //partition.get_iface().call_tree_node.clear_summaries();
//        for (auto it = partition.node_summaryID_set.begin(); it!=partition.node_summaryID_set.end(); ++it)
//           std::cout << "sumId_set " << *it;
//    }

    // Find partitions in the subtree suitable for summary extraction
    for (unsigned i = 1; i < partitions.size(); ++i) {
        partitiont& current_partition = partitions[i];

        // Mark the used summaries //should be a single summary per partition in UpProver
        if (current_partition.has_summary_representation() && !(current_partition.ignore)) {
            //for (auto summary_id : current_partition.partition_summary_ID_set) {
            auto summary_id = current_partition.get_iface().call_tree_node.get_node_sumID();
            current_partition.get_iface().call_tree_node.add_node_sumID(summary_id);
          //  }
        }

        if (!skip_partition(current_partition, store_summaries_with_assertion)){ //if has not abstract repr
            valid_tasks++;
//            std::cout << ";;create itp task for partition " << current_partition.get_iface().function_id.c_str() <<"\n";
//        } else{
//            std::cout << ";;skiped itp task for partition " << current_partition.get_iface().function_id.c_str() <<"\n";
        }
    }
    // Only do the interpolation if there are some interpolation tasks
    if (valid_tasks == 0)
        return;
    //report for UpProver
    std::cout << "\n### generated summaries at this stage: " << valid_tasks << "\n\n";
    
    interpolation_taskt itp_task(valid_tasks);
    //creates interpolation tasks that goes over the partitions and collects ids of partitions in subtree
    //that forms the A-part in interpolation problem ( pid: partitionID , tid: taskID).
    //for every partition you take the subtree of that partition as A-part and the rest is implicitly treated as B in opensmt
    for (unsigned pid = 1, tid = 0; pid < partitions.size(); ++pid) {
        partitiont& partition = partitions[pid];
        // for every partition u take the subtree of that partition
        if (!skip_partition(partition, store_summaries_with_assertion)){
            fill_partition_ids(pid, itp_task[tid++]);   //recursively fills childs id
        }
    }

    // Interpolate...
    //number of newly generated summaries = itp_result.size() = valid_tasks
    interpolantst itp_result;
    itp_result.reserve(valid_tasks);
    interpolator.get_interpolant(itp_task, itp_result);

    // Interpret the result
    for (unsigned pid = 1, tid = 0; pid < partitions.size(); ++pid) {
        partitiont& partition = partitions[pid];

        if (skip_partition(partition, store_summaries_with_assertion)) {
            continue;
        }

        auto itp = itp_result[tid];

        tid++;

        if (itp->is_trivial()) {
            std::cout << "Interpolant for function: " <<
                      partition.get_iface().function_id.c_str() << " is trivial." << std::endl;
            continue;
        }

        if (partition.get_iface().call_tree_node.is_recursion_nondet()){
            std::cout << "Skip interpolants for nested recursion calls.\n";
            continue;
        }

        // Generalize the interpolant
        auto common_symbs = partition.get_iface().get_iface_symbols();

#   ifdef DEBUG_ITP
        std::cout << "Interpolant for function: " <<
            partition.get_iface().function_id.c_str() << std::endl;
    std::cout << "Common symbols (" << common_symbs.size() << "):" << std::endl;
    for (std::vector<symbol_exprt>::iterator it = common_symbs.begin();
            it != common_symbs.end(); ++it)
      std::cout << it->get_identifier() << std::endl;

    std::cout << "Generalizing interpolant" << std::endl;
#   endif
        interpolator.generalize_summary(itp, common_symbs);

        if (itp->is_trivial()) {
            continue;
        }
        // Store the interpolant in summary_storet and asks a new ID for each summary
        auto new_id = summary_store.insert_summary(itp, id2string(partition.get_iface().function_id));
        partition.get_iface().call_tree_node.add_node_sumID(new_id);
        //for stat
        summary_store.generated_sumIDs.insert(new_id);
        // Update the precision information for omega deserialization; which partition
        //is now summarized?
        partition.get_iface().call_tree_node.set_summary();
    }
#else
    assert(0);
#endif
}
/*******************************************************************
 Function: partitioning_target_equationt::get_exprs_to_refine()

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/
std::vector<exprt> partitioning_target_equationt::get_exprs_to_refine() {
    std::vector<exprt> res;
    for (auto const & partition : partitions) {
        if (partition.ignore || partition.has_abstract_representation()) {continue;}
        assert(partition.is_real_ssa_partition());
        auto partition_beg = partition.start_it;
        auto partition_end = partition.end_it;
        for (auto it = partition_beg; it != partition_end; ++it) {
            if (it->ignore) { continue; }
            if (it->is_assignment()) {
                res.push_back(it->cond_expr);
            } else if (it->is_assert()) {
                // MB: copied from previous version
                exprt tmp(it->cond_expr);
                exprt fl = false_exprt();
                //fl.make_false();
                exprt op_ass = exprt(ID_equal);
                if (tmp.id() == ID_implies) {
                    exprt tr = true_exprt();
                    //tr.make_true();
                    exprt op_gua = exprt(ID_equal); //
                    op_gua.operands().push_back(tr);
                    op_gua.operands().push_back(tmp.operands()[0]);
                    res.push_back(op_gua);

                    op_ass.operands().push_back(tmp.operands()[1]);
                } else op_ass.operands().push_back(tmp);

                op_ass.operands().push_back(fl);
                res.push_back(op_ass);
            }
        }
    }
    return res;
}

void partitioning_target_equationt::convert_partition_guards(convertort &convertor, partitiont &partition) {
    ::convert_guards(convertor, partition.start_it, partition.end_it);
#ifdef DISABLE_OPTIMIZATIONS
    for(auto it = partition.start_it; it != partition.end_it; ++it) {
        if (it->ignore) { continue; }
        expr_ssa_print_guard(out_terms, it->guard, partition_smt_decl);
        if (!it->guard.is_boolean())
            terms_counter++; // SSA -> SMT shall be all in a new function
    }
#endif

}

void partitioning_target_equationt::convert_partition_assignments(convertort &convertor, partitiont &partition) {
    ::convert_assignments(convertor, partition.start_it, partition.end_it);
#ifdef DISABLE_OPTIMIZATIONS
    for(auto it = partition.start_it; it != partition.end_it; ++it) {
        if(it->is_assignment() && !it->ignore){
            expr_ssa_print(out_terms << "    ", it->cond_expr, partition_smt_decl, false);
            terms_counter++;
        }
    }
# endif
}

void partitioning_target_equationt::fill_function_templates(interpolating_solvert & interpolator,
                                                            std::vector<itpt_summaryt *> & templates) {
    for (partitionst::iterator it = partitions.begin(); it != partitions.end(); ++it) {
        auto & partition_iface = it->get_iface();
        auto iface_symbols = partition_iface.get_iface_symbols();
        std::string function_name = partition_iface.function_id.c_str();
        if(skip_partition_with_name(function_name)) { continue; }

        itpt_summaryt * sum = interpolator.create_stub_summary(function_name);
        if (sum) {
            interpolator.generalize_summary(sum, iface_symbols);
        }
        templates.push_back(sum);
    }
}
