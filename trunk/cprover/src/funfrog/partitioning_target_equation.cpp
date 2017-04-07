/*******************************************************************
 Module: Symex target equation which tracks different partitions for
 different deferred functions. Based on symex_target_equation.cpp.

 Author: Ondrej Sery

 \*******************************************************************/

#include <std_expr.h>

#include "partitioning_target_equation.h"
#include "expr_pretty_print.h"
#include "solvers/sat/cnf.h"
 
//#define DEBUG_SSA
//#define DEBUG_ITP
//#define DEBUG_ENCODING
//#define DEBUG_SSA_SMT_CALL // Before call to smt interface add a debug print

/*******************************************************************
 Function: partitioning_target_equationt::partitioning_target_equationt

 Inputs:

 Outputs:

 Purpose: Collects information about the specified partitions for later
 processing and conversion

 \*******************************************************************/

void partitioning_target_equationt::prepare_partitions() {
	// Fill in the partition start and end iterator for easier access during
	// the conversion process
	unsigned idx = 0;
	SSA_stepst::iterator ssa_it = SSA_steps.begin();

	// The last partition has an undefined end, fix it!
	if (!partitions.empty()) {
		partitions[current_partition_id].end_idx = SSA_steps.size();
	}

	for (partitionst::iterator it = partitions.begin(); it != partitions.end(); ++it) {

		assert(it->filled);
		bool ignore = true;

		it->start_it = ssa_it;

#   ifdef DEBUG_SSA
		std::cout << "Partition SSA indices: " << idx << ", " << it->start_idx
				<< ", " << it->end_idx << " size: " << partitions.size()
				<< std::endl;
#   endif

		if (it->summary || it->stub)
			continue;

		while (idx != it->end_idx) {
			assert(ssa_it != SSA_steps.end());
			ignore &= ssa_it->ignore;
			++ssa_it;
			++idx;
		}
		it->end_it = ssa_it;
		it->ignore = ignore & !it->get_iface().assertion_in_subtree;
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

			if (!partition.summary && !partition.stub)
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

		if (!partition.summary && !partition.stub)
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
	return NULL;
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

    if (partition.stub) {
        return;
    }

    assert( !partition.invalid && 
            (!partition.get_iface().assertion_in_subtree
                                    || store_summaries_with_assertion));

    if (partition.ignore) {
        assert(partition.child_ids.empty());
        return;
    }

    // Current partition id
    for (unsigned int i = 0; i < partition.fle_part_ids.size(); i++){
        part_ids.push_back(partition.fle_part_ids[i]);
    }

    assert(partition.is_inline() || partition.child_ids.empty());

    // Child partition ids
    for (partition_idst::iterator it = partition.child_ids.begin()++; it
                    != partition.child_ids.end(); ++it) {
        fill_partition_ids(*it, part_ids);
    }
}

/***************************************************************************/
std::ostream& partitioning_target_equationt::print_decl_smt(std::ostream& out) {
	if (partition_smt_decl->empty())
		return out;
	else {
		// Print all decl
		for (std::map<std::string, exprt>::iterator it =
				partition_smt_decl->begin(); it != partition_smt_decl->end(); ++it) {
			out << "(declare-fun " << it->first << ")" << std::endl;
		}

		// At the end of the loop
		partition_smt_decl->clear(); //Ready for the next partition
		return out;
	}
}

void partitioning_target_equationt::print_partition() {
	// When creating the real formula - do not add the assert here, check first if OpenSMT2 does it
	out_partition << "; " << basic_buf.str();
	if (terms_buf.str().length() > 0) {
		out_partition << "(assert\n";
		if (terms_counter > 1)
			out_partition << "  (and\n" << terms_buf.str() << "  )\n)" << endl;
		else
			out_partition << terms_buf.str() << ")" << endl;
	}

	// Init for reuse
	terms_buf.str("");
	basic_buf.str("");
	terms_counter = 0;
}

void partitioning_target_equationt::print_all_partition(std::ostream& out) {
	// Print only if the flag is on!
#   ifdef DEBUG_SSA_PRINT
	// Print header - not part of temp debug print!
	cout << "\nXXX SSA --> SMT-lib Translation XXX\n";

	// for prints later on
	std::ostream out_decl(0);
	std::stringbuf decl_buf;
	out_decl.rdbuf(&decl_buf);

	// When creating the real formula - do not add the assert here, check first if OpenSMT2 does it
	print_decl_smt(out_decl); // print the symbol decl
	cout << decl_buf.str() << partition_buf.str() << "(check-sat)\n";
#   endif
}

// Not in use here
void partitioning_target_equationt::addToDeclMap(const exprt &expr) {
    if (partition_smt_decl == NULL)
        return;

    std::ostream out_code(0);
    std::stringbuf code_buf;
    out_code.rdbuf(&code_buf);

    out_code << expr.id().c_str() << " " << expr.type().id();
    std::string key = code_buf.str();

    if (partition_smt_decl->find(key) == partition_smt_decl->end())
        partition_smt_decl->insert(make_pair(key, expr));
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
