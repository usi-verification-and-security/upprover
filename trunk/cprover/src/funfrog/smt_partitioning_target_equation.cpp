/*******************************************************************
 Module: Symex target equation which tracks different partitions for
 different deferred functions. Based on symex_target_equation.cpp.

 Author: Ondrej Sery

 \*******************************************************************/

#include <std_expr.h>

#include "smt_partitioning_target_equation.h"
#include "expr_pretty_print.h"
#include "solvers/sat/cnf.h"
#include "solvers/smtcheck_opensmt2.h"

//#define DEBUG_SSA_SMT_CALL // Before call to smt interface add a debug print

void
smt_partitioning_target_equationt::fill_function_templates(smtcheck_opensmt2t &decider, vector<summaryt*>& templates)
{
    for(partitionst::iterator it = partitions.begin(); it != partitions.end(); ++it)
    {
        vector<symbol_exprt> common;
        fill_common_symbols(*it, common);
        smt_summaryt *sum = new smt_summaryt();
        string fun_name = id2string(it->get_iface().function_id);
        decider.adjust_function(*sum, common, fun_name, false);
        templates.push_back(sum);
    }
}


/*******************************************************************
 Function: smt_partitioning_target_equationt::convert

 Inputs:

 Outputs:

 Purpose: Convert all the SSA steps into the corresponding formulas in
 the corresponding partitions

 \*******************************************************************/
void smt_partitioning_target_equationt::convert(smtcheck_opensmt2t &decider,
		interpolating_solvert &interpolator) {
    getFirstCallExpr(); // Save the first call to the first function

    decider.start_encoding_partitions();
    for (partitionst::reverse_iterator it = partitions.rbegin(); it
            != partitions.rend(); ++it) {
        convert_partition(decider, interpolator, *it);
        if (it->fle_part_id < 0) continue;

#   ifndef DEBUG_SSA_PRINT
        cout
#   else
        out_basic
#   endif
            << "XXX Partition: " << it->fle_part_id << " (ass_in_subtree: "
                << it->get_iface().assertion_in_subtree << ")" << " - "
                << it->get_iface().function_id.c_str() << " (loc: "
                << it->get_iface().summary_info.get_call_location() << ", "
                << ((it->summary) ? ((it->inverted_summary) ? "INV" : "SUM")
                    : ((it->stub) ? "TRU" : "INL")) << ")" << std::endl;

        // Print partition into a buffer after the headers: basic and code
        print_partition();
    }

    // Print all after the headers: decl and code
    print_all_partition(std::cout);
}

/*******************************************************************
 Function: smt_partitioning_target_equationt::convert_partition

 Inputs:

 Outputs:

 Purpose: Convert a specific partition of SSA steps

 \*******************************************************************/
void smt_partitioning_target_equationt::convert_partition(
		smtcheck_opensmt2t &decider, interpolating_solvert &interpolator,
		partitiont& partition) {
	if (partition.ignore || partition.processed || partition.invalid) {
#   ifdef DEBUG_ENCODING
		if (partition.invalid) {
			std::cout << "  partition invalidated (refined)." << std::endl;
		} else if (partition.ignore) {
			assert (!partition.get_iface().assertion_in_subtree);
			std::cout << "  partition sliced out." << std::endl;
		} else if (partition.processed) {
			std::cout << "  partition already processed." << std::endl;
		}
#	endif
		return;
	}
# ifdef DEBUG_SSA_SMT_CALL
	cout << "Before decider::convert - assumption propagation symbols" << endl;
# endif
	// Convert the assumption propagation symbols
	partition_ifacet &partition_iface = partition.get_iface();
	partition_iface.callstart_literal = decider.convert(
			partition_iface.callstart_symbol);
	partition_iface.callend_literal = decider.convert(
			partition_iface.callend_symbol);
	if (partition_iface.assertion_in_subtree) {
		partition_iface.error_literal = decider.convert(
				partition_iface.error_symbol);
	}
	if (partition.stub) {
#       ifdef DEBUG_ENCODING
			std::cout << "  partition havoced." << std::endl;
#	endif
		return;
	}

	//  if ((partition.summary &&
	//          partition.applicable_summaries.empty())) {
	//    assert(!partition.inverted_summary);
	//#   ifdef DEBUG_SSA
	//    std::cout << "  no applicable summary." << std::endl;
	//#	endif
	//    return;
	//  }

	// Tell the interpolator about the new partition.
	partition.set_fle_part_id(interpolator.new_partition());

	// If this is a summary partition, apply the summary
	if (partition.summary) {
		convert_partition_summary(decider, partition);
		// FIXME: Only use in the incremental solver mode (not yet implemented)
		// partition.processed = true;
		return;
	}

	// Reserve fresh variables for the partition boundary
	std::vector < symbol_exprt > common_symbs;
	fill_common_symbols(partition, common_symbs);

	// GF: hack
	//  smt_interpolantt::reserve_variables(decider, common_symbs, partition.get_iface().common_symbols);

	// Convert the corresponding SSA steps
	convert_partition_guards(decider, partition);
	convert_partition_assignments(decider, partition);
	convert_partition_assumptions(decider, partition);
	// if (partition.get_iface().function_id.c_str() == "c::main"){
	//   std::cout << "converting assertions\n";
	convert_partition_assertions(decider, partition);
	// } else {
	//   std::cout << "skipping converting assertions\n";
	// }
	convert_partition_io(decider, partition);
	// FIXME: Only use in the incremental solver mode (not yet implemented)
	// partition.processed = true;
}
/*******************************************************************
 Function: smt_partitioning_target_equationt::convert_partition_summary

 Inputs:

 Outputs:

 Purpose: Convert a summary partition (i.e., assert its summary)

 \*******************************************************************/

void smt_partitioning_target_equationt::convert_partition_summary(
		smtcheck_opensmt2t &decider, partitiont& partition) {
    std::vector < symbol_exprt > common_symbs;
    summary_storet* summary_store = summarization_context.get_summary_store();
    fill_common_symbols(partition, common_symbs);
    unsigned i = 0;

#   ifdef DEBUG_SSA
    std::cout << "Candidate summaries: " << partition.summaries->size()
                << std::endl;
#   endif

    bool is_recursive = partition.get_iface().summary_info.is_recursive(); //on_nondet();
    unsigned last_summary = partition.applicable_summaries.size() - 1;

    for (summary_ids_sett::const_iterator it =
                    partition.applicable_summaries.begin(); it
                    != partition.applicable_summaries.end(); ++it) {

        smt_summaryt& summary = dynamic_cast<smt_summaryt&> (summary_store->find_summary(*it));

        if (summary.is_valid() && (!is_recursive || last_summary == i++)) {
#ifdef DEBUG_SSA
            std::cout << "Substituting summary #" << *it << std::endl;
#endif
            summary.substitute(decider, common_symbs, partition.inverted_summary);
        }
    }
        
    summary_store = NULL;
}

/*******************************************************************
 Function: smt_partitioning_target_equationt::convert_partition_assignments

 Inputs:

 Outputs:

 Purpose: Convert a specific partition assignments of SSA steps

 \*******************************************************************/

void smt_partitioning_target_equationt::convert_partition_assignments(
		smtcheck_opensmt2t &decider, partitiont& partition) {
    for (SSA_stepst::const_iterator it = partition.start_it; it
            != partition.end_it; ++it) {

        if (it->is_assignment() && !it->ignore) {
            exprt tmp(it->cond_expr);

            // Only if not an assignment to rounding model print it + add it to LRA statements
            if (!isRoundModelEq(tmp)) {
#     ifdef DEBUG_SSA
                expr_pretty_print(std::cout << "ASSIGN-OUT:" << std::endl, tmp, 2);
                //expr_ssa_print_test(&partition_smt_decl, out_code << "(assign ", tmp);
#     endif
#     ifdef DEBUG_SSA_PRINT
                expr_ssa_print(out_terms << "    ", tmp, partition_smt_decl, false);
                terms_counter++;
#     endif
#     ifdef DEBUG_SSA_SMT_CALL
                expr_ssa_print_smt_dbg(
                cout << "Before decider::set_to_true(ASSIGN-OUT) --> ",
						tmp, false);
#     endif
                decider.set_to_true(tmp);
		exprs.push_back(tmp);
            }
        }
    }
}

bool smt_partitioning_target_equationt::isRoundModelEq(const exprt &expr) {
	if (!expr.has_operands())
		return false;
	if (expr.operands().size() > 2)
		return false;

	// Start checking if it is auto gen code for rounding model
	if (expr.operands().size() == 2) {
		string str = id2string((expr.operands()[1]).get(ID_identifier));
		if (str.find("__CPROVER_rounding_mode#") != std::string::npos)
			return true;
	}

	string str = id2string((expr.operands()[0]).get(ID_identifier));
	if (str.find("__CPROVER_rounding_mode#") != std::string::npos)
		return true;

	return false;
}

/*******************************************************************
 Function: smt_partitioning_target_equationt::convert_partition_guards

 Inputs:

 Outputs:

 Purpose: Convert a specific partition guards of SSA steps

 \*******************************************************************/

void smt_partitioning_target_equationt::convert_partition_guards(
		smtcheck_opensmt2t &decider, partitiont& partition) {
	for (SSA_stepst::iterator it = partition.start_it; it != partition.end_it; ++it) {
		if (it->ignore) {
#       ifdef DEBUG_SSA_SMT_CALL
            cout << "Before decider::const_var(GUARD-OUT) --> false" << endl;
#       endif
			it->guard_literal = decider.const_var(false);
		} else {
			exprt tmp(it->guard);
#       ifdef DEBUG_SSA_PRINT
			//expr_pretty_print(std::cout << "GUARD-OUT:" << std::endl, tmp, 2);
			expr_ssa_print_guard(out_terms, tmp, partition_smt_decl);
			if (!tmp.is_boolean())
				terms_counter++; // SSA -> SMT shall be all in a new function
#       endif
#       ifdef DEBUG_SSA_SMT_CALL
			expr_ssa_print_smt_dbg(
					cout << "Before decider::convert(GUARD-OUT) --> ", tmp,
					false);
#	endif
			it->guard_literal = decider.convert(tmp);
		}
	}
}

/*******************************************************************
 Function: smt_partitioning_target_equationt::convert_partition_assumptions

 Inputs:

 Outputs:

 Purpose: Convert a specific partition assumptions of SSA steps

 \*******************************************************************/

void smt_partitioning_target_equationt::convert_partition_assumptions(
		smtcheck_opensmt2t &decider, partitiont& partition) {
	for (SSA_stepst::iterator it = partition.start_it; it != partition.end_it; ++it) {
		if (it->is_assume()) {
			if (it->ignore) {
#     	ifdef DEBUG_SSA_SMT_CALL
				cout << "Before decider::const_var(ASSUME-OUT) --> true" << endl;
#	endif
				it->cond_literal = decider.const_var(true);
				// GF
			} else {
				exprt tmp(it->cond_expr);
#     	ifdef DEBUG_SSA_SMT_CALL
				expr_ssa_print_smt_dbg(
						cout << "Before decider::convert(ASSUME-OUT) --> ",
						tmp, false);
#	endif
				it->cond_literal = decider.convert(tmp);
			}
		}
	}
}

/*******************************************************************
 Function: smt_partitioning_target_equationt::convert_partition_assertions

 Inputs:

 Outputs:

 Purpose: Convert a specific partition assertions of SSA steps

 \*******************************************************************/

void smt_partitioning_target_equationt::convert_partition_assertions(
		smtcheck_opensmt2t &decider, partitiont& partition) {
	unsigned number_of_assertions = count_partition_assertions(partition);
	unsigned number_of_assumptions = 0;
	const partition_ifacet& partition_iface = partition.get_iface();

	bvt bv;
	if (partition_iface.assertion_in_subtree) {
		bv.reserve(number_of_assertions + partition.child_ids.size());
	}

# ifdef DEBUG_SSA_SMT_CALL
	cout << "Before decider::const_var(ASSERT-OUT) --> true" << endl;
# endif
	literalt assumption_literal = decider.const_var(true);
	for (SSA_stepst::iterator it = partition.start_it; it != partition.end_it; ++it) {

		if ((it->is_assert()) && !(it->ignore)) {
#       ifdef DEBUG_SSA_SMT_CALL
			bool test = (isTypeCastConst(it->cond_expr));
			expr_ssa_print_smt_dbg(
					cout << "Before decider::convert and decider.limplies(ASSERT-OUT) " << (test ? "w/t " : "no ") << "TYPECAST --> "
					, it->cond_expr, true);
#	endif
			// Collect ass \in assertions(f) in bv
			literalt tmp_literal = (decider.is_exist_var_constraints()) ?
					decider.land(decider.convert(it->cond_expr), decider.lassert_var())
					:decider.convert(it->cond_expr);
			it->cond_literal
					= decider.limplies(assumption_literal, tmp_literal);
			bv.push_back(decider.lnot(it->cond_literal));
		} else if (it->is_assume() && !it->ignore) {
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
				assert(
						!target_partition->invalid
								&& !target_partition->processed);

#		ifdef DEBUG_SSA_SMT_CALL
				expr_ssa_print_smt_dbg(
						cout << "Before decider::land(GUARD-LITERAL of Call-START) --> ",
						it->guard, false);
				expr_ssa_print_smt_dbg(
						cout << "Before decider::set_equal(Call-START) --> ",
						target_partition_iface.callstart_symbol, false);
#		endif
				literalt tmp = decider.land(assumption_literal,
						it->guard_literal);
				decider.set_equal(tmp, target_partition_iface.callstart_literal);
#		ifdef DEBUG_SSA_PRINT
				//out_terms << "XXX Call START equality: \n";
				terms_counter++;
				std::ostream out_temp2(0);
				std::stringbuf temp2_buf;
				out_temp2.rdbuf(&temp2_buf); // Pre-order printing
				int assume_counter = 0;
				expr_ssa_print(out_temp2 << "    (= ",
						target_partition_iface.callstart_symbol,
						partition_smt_decl, false);

				for (SSA_stepst::iterator it2 = partition.start_it; it2 != it; ++it2) {
					if (it2->is_assume() && !it2->ignore) {
						assume_counter++;
						expr_ssa_print(out_temp2 << "        ", it2->cond_expr,
								partition_smt_decl, false);
					}
				}
				// If there are more than one term - add and
				switch (assume_counter) {
				case 0:
					out_terms << temp2_buf.str() << "        true\n"
							<< "    )\n";
					break; // Shall be called only once at the beginning of the code
				case 1:
					out_terms << temp2_buf.str() << "    )\n";
					break;
				default:
					out_terms << "    (and \n  " << temp2_buf.str()
							<< "      )\n" << "    )\n";
					break;
				}
#	    endif
			}

			// Collect this assumption as:
			//
			//     assumption_literal = \land_{ass \in assumptions(f)} ass
			//
#           ifdef DEBUG_SSA_SMT_CALL
			cout << "Before decider::land(call-START) " << number_of_assumptions << endl;
#	    endif
			assumption_literal = decider.land(assumption_literal,
					it->cond_literal);
			number_of_assumptions++;
		}
	}

	for (partition_idst::const_iterator it = partition.child_ids.begin(); it
			!= partition.child_ids.end(); ++it) {
		const partitiont& target_partition = partitions[*it];

		if (target_partition.get_iface().assertion_in_subtree) {
			// Collect error_g, where g \in children(f) in bv
			bv.push_back(target_partition.get_iface().error_literal);
		}
	}

	// Encode the collected assertions:
	//
	// error_f <=>
	//     (\lor_{g \in children(f)} error_g) \lor
	//     (\lor_{ass \in assertions(f)} ass)
	//
	if (!bv.empty()) {
		assert(partition_iface.assertion_in_subtree);

		if (partition.parent_id == partitiont::NO_PARTITION
				&& !upgrade_checking) {
#       ifdef DEBUG_SSA_SMT_CALL
			cout << "Before decider::const_var(error in ROOT) --> true" << endl;
			cout << "Before decider::land(error in ROOT)" << endl;
#	endif
			decider.set_equal(decider.land(bv), decider.const_var(true));

#ifdef DEBUG_SSA_PRINT
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
			for (partition_idst::const_iterator it =
					partition.child_ids.begin(); it
					!= partition.child_ids.end(); ++it) {
				const partitiont& target_partition = partitions[*it];
				const partition_ifacet& target_partition_iface =
						target_partition.get_iface();

				if (!target_partition.ignore
						&& target_partition_iface.assertion_in_subtree) {
					assert_counter++;
					if (assert_counter == 1)
						expr_ssa_print(out_temp1,
								target_partition_iface.error_symbol,
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
#endif
		} else {
#               ifdef DEBUG_SSA_SMT_CALL
			cout << "Before decider::set_equal(ERROR) to " << bv.size()
					<< " literals" << endl;
#	        endif
			if (bv.size() == 1) { // Corner case: single literal for OR, it is just bv[0]
				decider.set_equal(bv[0], partition_iface.error_literal);
			} else {
				decider.set_equal(decider.lor(bv),
						partition_iface.error_literal);
			}

#ifdef DEBUG_SSA_PRINT
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
			for (partition_idst::const_iterator it =
					partition.child_ids.begin(); it
					!= partition.child_ids.end(); ++it) {
				const partitiont& target_partition = partitions[*it];
				const partition_ifacet& target_partition_iface =
						target_partition.get_iface();

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
			for (symex_target_equationt::SSA_stepst::iterator it2 =
					partition.start_it; it2 != partition.end_it; ++it2) {
				if (it2->is_assume() && !it2->ignore) {
					assume_counter++;
					expr_ssa_print(out_temp_assume << "            ",
							it2->cond_expr, partition_smt_decl, false);
				}
			}
			std::string assume_code = "";
			if (assume_counter > 1)
				assume_code = "          (and \n" + temp_assume_buf.str()
						+ "          )\n";
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
	//    #ifdef DEBUG_SSA
	//    expr_pretty_print(std::cout << "XXX Asserting error_root: ",
	//            partition_iface.error_symbol);
	//    #endif
	//  }

	if (partition.parent_id != partitiont::NO_PARTITION) {
		assert(number_of_assumptions > 0);
		// Encode callend propagation formula for the partition:
		//
		// callend_f =>
		//     (\land_{ass \in assumptions(f)} ass)
		//
		// NOTE: callstart_f \in assumptions(f)
		//
#   ifdef DEBUG_SSA_SMT_CALL
		cout << "Before decider::limplies(CALL-END)" << endl;
#	endif
		literalt tmp_end = decider.limplies(partition_iface.callend_literal, assumption_literal); // BUG!! - before didn't not use the result of it
		decider.set_equal(tmp_end, decider.const_var(true)); // KE: maybe that's the missing call?

#   ifdef DEBUG_SSA_PRINT
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
			out_terms << "\n      (and \n" << temp_buf.str() << "      )\n"
					<< "    )\n";
		else
			out_terms << "\n" << temp_buf.str() << "    )\n";
#   endif
	}
}

/*******************************************************************
 Function: smt_partitioning_target_equationt::convert_partition_io

 Inputs:

 Outputs:

 Purpose: Convert a specific partition io of SSA steps

 \*******************************************************************/

void smt_partitioning_target_equationt::convert_partition_io(
		smtcheck_opensmt2t &decider, partitiont& partition) {
    for (SSA_stepst::iterator it = partition.start_it; it != partition.end_it; ++it)
        if (!it->ignore) {
            for (std::list<exprt>::const_iterator o_it = it->io_args.begin(); o_it
                            != it->io_args.end(); ++o_it) {
                exprt tmp = *o_it;
                if (tmp.is_constant() || tmp.id() == ID_string_constant)
                    it->converted_io_args.push_back(tmp);
                else {
                    symbol_exprt symbol(("symex::io::"+std::to_string(io_count_global++)), tmp.type());

#ifdef DEBUG_SSA_SMT_CALL
                    expr_ssa_print_smt_dbg(cout << "Before decider::set_to_true --> ",
                        equal_exprt(tmp, symbol), false);
#endif
                    decider.set_to_true(equal_exprt(tmp, symbol));
                    it->converted_io_args.push_back(symbol);
                }
            }
        }
}

/*******************************************************************
 Function: smt_partitioning_target_equationt::extract_interpolants

 Inputs:

 Outputs:

 Purpose: Extract interpolants corresponding to the created partitions

 \*******************************************************************/
void smt_partitioning_target_equationt::extract_interpolants(
		interpolating_solvert& interpolator, const smtcheck_opensmt2t& decider,
		interpolant_mapt& interpolant_map) {
    // Prepare the interpolation task. NOTE: ignore the root partition!
    unsigned valid_tasks = 0;
    summary_storet* summary_store = summarization_context.get_summary_store();

    // Clear the used summaries
    for (unsigned i = 0; i < partitions.size(); ++i)
            partitions[i].get_iface().summary_info.clear_used_summaries();

    // Find partitions suitable for summary extraction
    for (unsigned i = 1; i < partitions.size(); ++i) {
            partitiont& partition = partitions[i];

            // Mark the used summaries
            if (partition.summary && !(partition.ignore || partition.invalid)) {
                    for (summary_ids_sett::const_iterator it =
                                    partition.applicable_summaries.begin(); it
                                    != partition.applicable_summaries.end(); ++it) {
                            partition.get_iface().summary_info.add_used_summary(*it);
                    }
            }

            if (!partition.is_inline()
                            || (partition.get_iface().assertion_in_subtree
                                            && !store_summaries_with_assertion)
                            || partition.get_iface().summary_info.is_recursion_nondet())
                    continue;

            valid_tasks++;
    }

    // Only do the interpolation if there are some interpolation tasks
    if (valid_tasks == 0)
        return;

    interpolation_taskt itp_task(valid_tasks);

    for (unsigned pid = 1, tid = 0; pid < partitions.size(); ++pid) {
        partitiont& partition = partitions[pid];
        partition_ifacet ipartition = partition.get_iface();
        if (!partition.is_inline() || (ipartition.assertion_in_subtree
                && !store_summaries_with_assertion)
                || partition.get_iface().summary_info.is_recursion_nondet())
            continue;
        fill_partition_ids(pid, itp_task[tid++]);
    }

    // Interpolate...
    interpolantst itp_result;
    itp_result.reserve(valid_tasks);
    interpolator.get_interpolant(itp_task, itp_result);

    // Interpret the result
    std::vector < symbol_exprt > common_symbs;
    interpolant_map.reserve(valid_tasks);
    for (unsigned pid = 1, tid = 0; pid < partitions.size(); ++pid) {
        partitiont& partition = partitions[pid];

        if (!partition.is_inline()
                || (partition.get_iface().assertion_in_subtree
                    && !store_summaries_with_assertion)
                || partition.get_iface().summary_info.is_recursion_nondet())
            continue;

        smt_itpt *itp = dynamic_cast <smt_itpt*> (itp_result[tid]);

        tid++;

        if (itp->is_trivial()) {
            std::cout << "Interpolant for function: "
                            << partition.get_iface().function_id.c_str()
                            << " is trivial." << std::endl;
            continue;
        }

        if (partition.get_iface().summary_info.is_recursion_nondet()) {
            std::cout << "Skip interpolants for nested recursion calls.\n";
            continue;
        }

        // Generalize the interpolant
        fill_common_symbols(partition, common_symbs);

#   ifdef DEBUG_ITP
        std::cout << "Interpolant for function: " <<
        partition.get_iface().function_id.c_str() << std::endl;
        std::cout << "Common symbols (" << common_symbs.size() << "):" << std::endl;
        for (std::vector<symbol_exprt>::iterator it = common_symbs.begin();
                        it != common_symbs.end(); ++it)
            std::cout << it->get_identifier() << std::endl;

        std::cout << "Generalizing interpolant" << std::endl;
#   endif

        // GF: hack
        //    itp.generalize(decider, common_symbs);

        if (itp->is_trivial()) {
            continue;
        }

        string fun_name = id2string(partition.get_iface().function_id);
        interpolator.adjust_function(*itp, common_symbs, fun_name);

        // Store the interpolant
        summary_idt summary_id = summary_store->insert_summary(*itp);

        interpolant_map.push_back(interpolant_mapt::value_type(&partition.get_iface(), summary_id));
    }
    
    summary_store = NULL;
}
