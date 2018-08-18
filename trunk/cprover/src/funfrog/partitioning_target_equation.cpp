/*******************************************************************
 Module: Symex target equation which tracks different partitions for
 different deferred functions. Based on symex_target_equation.cpp.

 Author: Ondrej Sery

 \*******************************************************************/

#include "partitioning_target_equation.h"
#include "partition_iface.h"
#include "solvers/check_opensmt2.h"
#include "utils/naming_helpers.h"
#include "summary_store.h"
#include "conversion_utils.h"

#include <numeric>
#include <algorithm>

using namespace hifrog;

partitioning_target_equationt::partitioning_target_equationt(
  const namespacet & _ns,
  summary_storet & summary_store,
  bool _store_summaries_with_assertion) :
  symex_target_equationt(_ns),
  current_partition_id(NO_PARTITION_ID),
#         ifdef DISABLE_OPTIMIZATIONS
    dump_SSA_tree(false),
    ssa_tree_file_name("__ssa_tree.smt2"),
    out_local_terms(0),
    out_terms(out_local_terms),
    out_local_basic(0),
    out_basic(out_local_basic),
    out_local_partition(0),
    out_partition(out_local_partition),
    terms_counter(0),
    is_first_call(true),
    first_call_expr(0),
#endif
  io_count_global(0),
  summary_store{summary_store},
  store_summaries_with_assertion(_store_summaries_with_assertion)
  {
#ifdef DISABLE_OPTIMIZATIONS
    partition_smt_decl = new std::map <std::string,exprt>();
    out_terms.rdbuf(&terms_buf);
    out_basic.rdbuf(&basic_buf);
    out_partition.rdbuf(&partition_buf);
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

/*******************************************************************
 Function: partitioning_target_equationt::invalidate_partition

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/
//void partitioning_target_equationt::invalidate_partition(partition_idt partition_id)
//{
//    partitiont& partition = partitions[partition_id];
//
//    partition.invalid = true;
//    partition_map.erase(partition.get_iface().callend_symbol.get_identifier());
//
//    if (partition.parent_id != partitiont::NO_PARTITION) {
//        partitions[partition.parent_id].remove_child_partition(partition_id);
//    }
//}

void partitioning_target_equationt::refine_partition(partition_idt partition_id)
{
    partitiont& partition = partitions[partition_id];

    if(! partition.has_abstract_representation()){
        throw std::logic_error{"Trying to refine a pertition that was not summarized or stubbed before!"};
    }
    partition.remove_abstract_representation();
    partition.summaries.clear();
    partition.applicable_summaries.clear();
}



void partitioning_target_equationt::fill_summary_partition(partition_idt partition_id, const summary_idst & summaries)
{
    if(summaries.empty()){
        throw std::logic_error{"Trying to set non-existent summaries to a partition"};
    }
    partitiont& sum_partition = partitions.at(partition_id);

    sum_partition.add_summary_representation();
    sum_partition.summaries = summaries;

    sum_partition.applicable_summaries.clear();
    for (unsigned long summary_id : summaries) {
        sum_partition.applicable_summaries.insert(summary_id);
    }
}

/*******************************************************************
 Function: partitioning_target_equationt::partitioning_target_equationt

 Inputs:

 Outputs:

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

 Purpose: Fill in ids of all the child partitions

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
    for(auto id : partition.get_fle_part_ids()){
        part_ids.push_back(id);
    }

    // Child partition ids
    for (auto child_id : partition.child_ids) {
        fill_partition_ids(child_id, part_ids);
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

//void partitioning_target_equationt::fill_inverted_summary_partition(
//  partition_idt partition_id, const summary_idst * summaries, const summary_ids_sett & used_summaries) {
//    partitiont & sum_partition = partitions.at(partition_id);
//    assert(!sum_partition.filled);
//
//    sum_partition.filled = true;
//    sum_partition.summary = true;
//    sum_partition.inverted_summary = true;
//    sum_partition.summaries = summaries;
//    sum_partition.used_summaries = used_summaries;
//    sum_partition.applicable_summaries = used_summaries;
//
////    Commented out for now to remove dependency on iostream, this method is not used at the moment anyway
////    std::cerr << "  --- (" << partition_id <<
////              ") sums: " << sum_partition.summaries->size() <<
////              " used: " << sum_partition.used_summaries.size() << std::endl;
//}

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
    out_partition << "; " << basic_buf.str();
    if (terms_buf.str().length() > 0) {
        out_partition << "(assert\n";
        if (terms_counter > 1)
            out_partition << "  (and\n" << terms_buf.str() << "  )\n)" << '\n';
        else
            out_partition << terms_buf.str() << ")" << '\n';
    }

    // Init for reuse
    terms_buf.str("");
    basic_buf.str("");
    terms_counter = 0;
}

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
    out << decl_buf.str() << partition_buf.str() << "(check-sat)\n";
}

void partitioning_target_equationt::getFirstCallExpr() 
{
    saveFirstCallExpr(partitions.at(1).get_iface().callstart_symbol);
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
 Function: smt_partitioning_target_equationt::convert_partition_assertions

 Inputs:

 Outputs:

 Purpose: Convert a specific partition assertions of SSA steps

 \*******************************************************************/

void partitioning_target_equationt::convert_partition_assertions(
        check_opensmt2t &decider, partitiont& partition)
{
    unsigned number_of_assumptions = 0;
    const partition_ifacet& partition_iface = partition.get_iface();

    bvt error_lits;

    literalt assumption_literal = decider.get_const_literal(true);
    for (auto it = partition.start_it; it != partition.end_it; ++it) {
        if(it->ignore) {continue;} // ignored instructions can be skippied
        if (it->is_assert()) {

            // Collect ass \in assertions(f) in bv
            // FIXME add constraints
//            literalt tmp_literal = (decider.is_exist_var_constraints()) ?
//                                    decider.land(decider.convert(it->cond_expr), decider.lassert_var())
//                                    :decider.convert(it->cond_expr);
            literalt tmp_literal = decider.bool_expr_to_literal(it->cond_expr);
            it->cond_literal = decider.limplies(assumption_literal, tmp_literal);
            error_lits.push_back(!it->cond_literal); // negated literal
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

                literalt tmp = decider.land(assumption_literal,it->guard_literal);
                decider.set_equal(tmp, target_partition_iface.callstart_literal);

#		ifdef DISABLE_OPTIMIZATIONS
                //out_terms << "XXX Call START equality: \n";
                    terms_counter++;
                    std::ostream out_temp2(0);
                    std::stringbuf temp2_buf;
                    out_temp2.rdbuf(&temp2_buf); // Pre-order printing
                    int assume_counter = 0;
                    expr_ssa_print(out_terms << "    (= ",
                        target_partition_iface.callstart_symbol, partition_smt_decl, false);

                    for (SSA_stepst::iterator it2 = partition.start_it; it2 != it; ++it2) {
                        if (it2->is_assume() && !it2->ignore) {
                            assume_counter++;
                            expr_ssa_print(out_temp2 << "        ", it2->cond_expr, partition_smt_decl, false);
                        }
                    }
                    // If there are more than one term - add and
                    switch (assume_counter) {
                    case 0:
                        out_terms << temp2_buf.str() << "        true\n" << "    )\n";
                        break; // Shall be called only once at the beginning of the code
                    case 1:
                        out_terms << temp2_buf.str() << "    )\n";
                        break;
                    default:
                        out_terms << "      (and \n" << temp2_buf.str() << "      )\n" << "    )\n";
                        break;
                    }
#               endif
            }

            // Collect this assumption as:
            //
            //     assumption_literal = \land_{ass \in assumptions(f)} ass
            //
            assumption_literal = decider.land(assumption_literal, it->cond_literal);
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

        if (!partition.has_parent()) {
            decider.lcnf(error_lits);

#       ifdef DISABLE_OPTIMIZATIONS
            //out_terms << "XXX Encoding error in ROOT: " << std::endl;

            // Pre-order printing
            std::ostream out_temp1(0);
            std::stringbuf temp1_buf;
            out_temp1.rdbuf(&temp1_buf);

            int assert_counter = 0;
            for (SSA_stepst::iterator it = partition.start_it; it
                            != partition.end_it; ++it) {
                if (it->is_assert() && !it->ignore) {
                    assert_counter++;
                    if (assert_counter == 1)
                        expr_ssa_print(out_temp1, it->cond_expr,
                                        partition_smt_decl, false);
                    else
                        expr_ssa_print(out_temp1 << "        ", it->cond_expr,
                                        partition_smt_decl, false);
                }
            }
            for (partition_idst::const_iterator it = partition.child_ids.begin();
                    it != partition.child_ids.end(); ++it) {
                const partitiont& target_partition = partitions[*it];
                const partition_ifacet& target_partition_iface =
                                                target_partition.get_iface();

                if (!target_partition.ignore
                                    && target_partition_iface.assertion_in_subtree) {
                    assert_counter++;
                    if (assert_counter == 1)
                        expr_ssa_print(out_temp1, target_partition_iface.error_symbol,
                                                partition_smt_decl, false);
                    else
                        expr_ssa_print(out_temp1 << "        ",
                                                target_partition_iface.error_symbol,
                                                partition_smt_decl, false);
                }
            }
            if (assert_counter > 0) {
                terms_counter++;
                if (assert_counter == 1)
                    out_terms << "    " << temp1_buf.str().substr(4);
                else
                    out_terms << "    (or \n      (" << temp1_buf.str()
                                            << "      )\n" << "    )\n";
            }
#       endif
        } else {
            decider.set_equal(decider.lor(error_lits), partition_iface.error_literal);
#ifdef DISABLE_OPTIMIZATIONS
            //out_terms << "XXX Encoding error_f: \n";
            terms_counter++;
            expr_ssa_print(out_terms << "    (= ",
                            partition_iface.error_symbol, partition_smt_decl, false);
            std::ostream out_temp_assert(0);
            std::stringbuf temp_assert_buf;
            out_temp_assert.rdbuf(&temp_assert_buf); // Pre-order printing
            int assert_counter = 0;
            for (SSA_stepst::iterator it = partition.start_it; it
                            != partition.end_it; ++it) {
                if (it->is_assert() && !it->ignore) {
                    assert_counter++;
                    expr_ssa_print(out_temp_assert << "          ",
                                it->cond_expr, partition_smt_decl, false);
                }
            }
            for (partition_idst::const_iterator it = partition.child_ids.begin();
                        it != partition.child_ids.end(); ++it) {
                const partitiont& target_partition = partitions[*it];
                const partition_ifacet& target_partition_iface = target_partition.get_iface();

                if (!target_partition.ignore
                                    && target_partition_iface.assertion_in_subtree) {
                    assert_counter++;
                    expr_ssa_print(out_temp_assert << "          ",
                                        target_partition_iface.error_symbol,
                                        partition_smt_decl, false);
                }
            }
            std::ostream out_temp_assume(0);
            std::stringbuf temp_assume_buf;
            out_temp_assume.rdbuf(&temp_assume_buf); // Pre-order printing
            int assume_counter = 0;
            for (symex_target_equationt::SSA_stepst::iterator it2 = partition.start_it;
                        it2 != partition.end_it; ++it2) {
                if (it2->is_assume() && !it2->ignore) {
                    assume_counter++;
                    expr_ssa_print(out_temp_assume << "            ",
                                    it2->cond_expr, partition_smt_decl, false);
                }
            }
            std::string assume_code = "";
            if (assume_counter > 1)
                assume_code = "          (and \n" + temp_assume_buf.str() + "          )\n";
            else
                assume_code = temp_assume_buf.str();
            if (assert_counter > 0) {
                terms_counter++;
                if (assert_counter == 1)
                    out_terms << "      (not\n        (=>\n" << assume_code
                                << temp_assert_buf.str()
                                << "        )\n      )\n    )\n";
                else
                    out_terms << "      (not\n        (=>\n" << assume_code
                                << "          (or \n  " << temp_assert_buf.str()
                                << "          )\n        )\n      )\n    )\n";
            }
#endif
        }
    }

    //  // Emit error_root = true for the ROOT partition
    //  if (partition.parent_id == partitiont::NO_PARTITION) {
    //    decider.prop.l_set_to_true(partition_iface.error_literal);
    //    #if defined(DEBUG_SSA) && defined(DISABLE_OPTIMIZATIONS)
    //    expr_pretty_print(std::cout << "XXX Asserting error_root: ",
    //            partition_iface.error_symbol);
    //    #endif
    //  }

    if (partition.has_parent()) {
        assert(number_of_assumptions > 0);
        // Encode callend propagation formula for the partition:
        //
        // callend_f =>
        //     (\land_{ass \in assumptions(f)} ass)
        //
        // NOTE: callstart_f \in assumptions(f)
        //

        literalt tmp = decider.limplies(partition_iface.callend_literal, assumption_literal);
        decider.assert_literal(tmp);

#       ifdef DISABLE_OPTIMIZATIONS
        //out_terms << "XXX Call END implication: \n";
        terms_counter++;
        expr_ssa_print(out_terms << "    (=> ", partition_iface.callend_symbol,
                        partition_smt_decl, false, true);
        std::ostream out_temp(0);
        std::stringbuf temp_buf;
        out_temp.rdbuf(&temp_buf); // Pre-order printing
        int assume_counter = 0;
        for (symex_target_equationt::SSA_stepst::iterator it2 =
                        partition.start_it; it2 != partition.end_it; ++it2) {
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
            out_terms << "\n      (and \n" << temp_buf.str() << "      )\n" << "    )\n";
        else
            out_terms << "\n" << temp_buf.str() << "    )\n";
#   endif
    }
}

/*******************************************************************
 Function: partitioning_target_equationt::convert_partition_goto_instructions

 Inputs:

 Outputs:

 Purpose: Convert a specific partition go-tos of SSA steps

 *  KE: added after the cprover upgrade
 \*******************************************************************/
void partitioning_target_equationt::convert_partition_goto_instructions(
        check_opensmt2t &decider, partitiont& partition)
{
    for (auto it = partition.start_it; it != partition.end_it; ++it) {
        if (it->is_goto()) {
            it->cond_literal = it->ignore ? const_literal(true) : decider.bool_expr_to_literal(it->cond_expr);
        }
    }
}

/*******************************************************************
 Function: partitioning_target_equationt::convert_partition_assumptions

 Inputs:

 Outputs:

 Purpose: Convert a specific partition assumptions of SSA steps

 \*******************************************************************/

void partitioning_target_equationt::convert_partition_assumptions(
        check_opensmt2t &decider, partitiont& partition) {
    for (auto it = partition.start_it; it != partition.end_it; ++it) {
        if (it->is_assume()) {
            it->cond_literal = it->ignore ? const_literal(true) : decider.bool_expr_to_literal(it->cond_expr);
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
        check_opensmt2t & decider, partitiont & partition) {
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
                    decider.set_to_true(equal_exprt(tmp, symbol));
                    it->converted_io_args.push_back(symbol);
                }
            }
        }
    }
}

/*******************************************************************
 Function: smt_partitioning_target_equationt::convert_partition_summary

 Inputs:

 Outputs:

 Purpose: Convert a summary partition (i.e., assert its summary)

 \*******************************************************************/

void partitioning_target_equationt::convert_partition_summary(
        check_opensmt2t & decider, partitiont & partition)
{
    auto common_symbs = partition.get_iface().get_iface_symbols();
    unsigned i = 0;

    bool is_recursive = partition.get_iface().call_tree_node.is_recursive(); //on_nondet();
    unsigned last_summary = partition.applicable_summaries.size() - 1;

    for (auto summary_id : partition.applicable_summaries)
    {
        auto & summary = summary_store.find_summary(summary_id);
        if ((!is_recursive || last_summary == i++)) {
            // we do not want to actually change the summary, because we might need the template later,
            // we just get a PTRef to the substituted version
            decider.insert_substituted(summary, common_symbs);
        }
    }
}

/*******************************************************************
 Function: partitioning_target_equationt::convert_partition

 Inputs:

 Outputs:

 Purpose: Convert a specific partition of SSA steps

 \*******************************************************************/
void partitioning_target_equationt::convert_partition(
        check_opensmt2t & decider, interpolating_solvert & interpolator,
        partitiont & partition) {
    if (partition.ignore) {
        return;
    }
    // Convert the assumption propagation symbols
    partition_ifacet &partition_iface = partition.get_iface();
    partition_iface.callstart_literal = decider.bool_expr_to_literal(
            partition_iface.callstart_symbol);
    partition_iface.callend_literal = decider.bool_expr_to_literal(
            partition_iface.callend_symbol);
    if (partition_iface.assertion_in_subtree) {
        partition_iface.error_literal = decider.bool_expr_to_literal(partition_iface.error_symbol);
    }
    if (partition.is_stub()) {
        return;
    }

    // Tell the interpolator about the new partition.
    partition.add_fle_part_id(interpolator.new_partition());

    // If this is a summary partition, apply the summary
    if (partition.has_summary_representation()) {
        convert_partition_summary(decider, partition);
        return;
    }
    // Convert the corresponding SSA steps
    auto partition_beg = partition.start_it;
    auto partition_end = partition.end_it;
    ::convert_guards(decider, partition_beg, partition_end);
    ::convert_assignments(decider, partition_beg, partition_end);
    convert_partition_assumptions(decider, partition);
    convert_partition_assertions(decider, partition);
    convert_partition_io(decider, partition);
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
 Function: partitioning_target_equationt::convert

 Inputs:

 Outputs:

 Purpose: Convert all the SSA steps into the corresponding formulas in
 the corresponding partitions

 \*******************************************************************/
void partitioning_target_equationt::convert(check_opensmt2t &decider,
                                                interpolating_solvert &interpolator) {
#ifdef DISABLE_OPTIMIZATIONS
    getFirstCallExpr(); // Save the first call to the first function
#endif
    for (auto it = partitions.rbegin(); it != partitions.rend(); ++it) {
        convert_partition(decider, interpolator, *it);
    }

#ifdef DISABLE_OPTIMIZATIONS
    if (dump_SSA_tree)
      {
        ofstream out_ssaT;
        out_ssaT.open(ssa_tree_file_name+"_"+std::to_string(get_unique_index())+".smt2");

        // Print all after the headers: decl and code
        print_all_partition(out_ssaT);

        out_ssaT.close();
      }
#endif
}

void partitioning_target_equationt::extract_interpolants(check_opensmt2t & decider) {
#ifdef PRODUCE_PROOF
    // Prepare the interpolation task. NOTE: ignore the root partition!
    unsigned valid_tasks = 0;

    // Clear the used summaries
    for (auto const & partition : partitions){
        partition.get_iface().call_tree_node.clear_used_summaries();
    }

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
        decider.generalize_summary(itp, common_symbs);

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

std::vector<exprt> partitioning_target_equationt::get_exprs_to_refine() {
    std::vector<exprt> res;
    for (auto const & partition : partitions) {
        if (partition.ignore) {continue;}
        assert(!partition.has_abstract_representation());
        auto partition_beg = partition.start_it;
        auto partition_end = partition.end_it;
        for (auto it = partition_beg; it != partition_end; ++it) {
            if (it->ignore) { continue; }
            if (it->is_assignment()) {
                res.push_back(it->cond_expr);
            } else if (it->is_assert()) {
                // MB: copied from previous version
                exprt tmp(it->cond_expr);
                exprt fl;
                fl.make_false();
                exprt op_ass = exprt(ID_equal);
                if (tmp.id() == ID_implies) {
                    exprt tr;
                    tr.make_true();

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
