/*******************************************************************
 Module: Symex target equation which tracks different partitions for
 different deferred functions. Based on symex_target_equation.cpp.

 Author: Ondrej Sery

 \*******************************************************************/

#include "partitioning_target_equation.h"
#include "partition_iface.h"

#include <numeric>
#include <algorithm>

partitioning_target_equationt::partitioning_target_equationt(
  const namespacet & _ns,
  summary_storet & summary_store,
  bool _store_summaries_with_assertion) :
  symex_target_equationt(_ns),
  current_partition_id(partitiont::NO_PARTITION),
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

    if (parent_id != partitiont::NO_PARTITION) {
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
 Function: partitioning_target_equationt::fill_common_symbols

 Inputs:

 Outputs:

 Purpose:

 \*******************************************************************/
void partitioning_target_equationt::fill_common_symbols(const partitiont& partition,
                         std::vector<symbol_exprt>& common_symbols) const
{
    common_symbols.clear();
    const partition_ifacet& iface = partition.get_iface();
    common_symbols.reserve(iface.argument_symbols.size() +
                           iface.out_arg_symbols.size()+4);
    common_symbols = iface.argument_symbols; // Add SSA instances of funcs
    common_symbols.insert(common_symbols.end(),
                          iface.out_arg_symbols.begin(),
                          iface.out_arg_symbols.end()); // Add globals
    common_symbols.push_back(iface.callstart_symbol);
    common_symbols.push_back(iface.callend_symbol);
    if (iface.assertion_in_subtree) {
        common_symbols.push_back(iface.error_symbol);
    }
    if (iface.returns_value) {
        common_symbols.push_back(iface.retval_symbol);
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
    if (current_partition_id != partitiont::NO_PARTITION) {
        auto & partition = get_current_partition();
        partition.end_idx = SSA_steps.size();
        assert(!partition.has_ssa_representation());
        partition.add_ssa_representation();
        current_partition_id = partitiont::NO_PARTITION;
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
