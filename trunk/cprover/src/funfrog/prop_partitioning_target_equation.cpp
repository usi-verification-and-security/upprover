
/*******************************************************************\

Module: Symex target equation which tracks different partitions for
different deferred functions. Based on symex_target_equation.cpp.

Author: Ondrej Sery

\*******************************************************************/

#include <std_expr.h>

#include "prop_partitioning_target_equation.h"
#include "expr_pretty_print.h"
#include "solvers/sat/cnf.h"
#include "solvers/satcheck_opensmt2.h"

//#define DEBUG_ITP // ITP of SAT - testing

/*******************************************************************\

 Function: prop_partitioning_target_equationt::convert

 Inputs:

 Outputs:

 Purpose: Convert all the SSA steps into the corresponding formulas in
 the corresponding partitions

\*******************************************************************/
void prop_partitioning_target_equationt::convert(prop_conv_solvert &prop_conv,
          interpolating_solvert &interpolator)
{
#ifdef DEBUG_SSA_PRINT    
    getFirstCallExpr(); // Save the first call to the first function
#endif  

    // KE: prop_conv change into prop_conv_solvert and use it from here - does cast + error check
    //prop_conv_solvert&prop_conv_solver = dynamic_cast<prop_conv_solvert&> (prop_conv);
    //assert(prop_conv_solver != 0); // KE: if null it says we never created it as prop_conv_solver - go back to prop_assertion_sum and fix it!      
  int part_id = partitions.size();
  for (partitionst::reverse_iterator it = partitions.rbegin();
          it != partitions.rend(); ++it) {
      --part_id; // dec the counter NOT in a print statement
#   ifdef DEBUG_ENCODING
    unsigned vars_before = prop_conv.prop.no_variables();
    unsigned clauses_before = dynamic_cast<cnf_solvert&>(prop_conv.prop).no_clauses();
#   endif
#   ifdef DEBUG_SSA    
    cout << "XXX Partition: " << part_id <<
            " (ass_in_subtree: " << it->get_iface().assertion_in_subtree << ")" << 
            " - " << it->get_iface().function_id.c_str() <<
            " (loc: " << it->get_iface().summary_info.get_call_location() << ", " <<
            ((it->summary) ? ((it->inverted_summary) ? "INV" : "SUM") :
                ((it->stub) ? "TRU" : "INL")) << ")" <<
            std::endl;
#   endif
    // For debugging of the SSA to SMT encoding
#   ifdef DEBUG_SSA_PRINT
        out_basic << "XXX Partition: " << part_id <<
            " (ass_in_subtree: " << it->get_iface().assertion_in_subtree << ")" << 
            " - " << it->get_iface().function_id.c_str() <<
            " (loc: " << it->get_iface().summary_info.get_call_location() << ", " <<
            ((it->summary) ? ((it->inverted_summary) ? "INV" : "SUM") :
                ((it->stub) ? "TRU" : "INL")) << ")" <<
            std::endl;
#   endif
    
    convert_partition(prop_conv, interpolator, *it);

    // Print partition into a buffer after the headers: basic and code
#ifdef DEBUG_SSA_PRINT    
    print_partition();
#endif    

#   ifdef DEBUG_ENCODING
    unsigned vars_after = prop_conv.prop.no_variables();
    unsigned clauses_after = dynamic_cast<cnf_solvert&>(prop_conv.prop).no_clauses();
    it->clauses = clauses_after - clauses_before;
    it->vars = vars_after - vars_before;
    std::cout << "    vars: " << it->vars << std::endl <<
            "    clauses: " << it->clauses << std::endl;
   // std::cout << "    last_var: " << dynamic_cast<satcheck_opensmtt&>(prop_conv.prop).get_last_var() << std::endl;

    unsigned clauses_total = it->clauses;
    unsigned vars_total = it->vars;

    for (partition_idst::const_iterator it2 = it->child_ids.begin();
            it2 != it->child_ids.end(); ++it2) {
      clauses_total += partitions[*it2].clauses;
      vars_total += partitions[*it2].vars;
    }

    std::cout << "    vars in subtree: " << vars_total << std::endl <<
            "    clauses in subtree: " << clauses_total << std::endl;

    it->clauses = clauses_total;
    it->vars = vars_total;
#   endif
  }

# ifdef DEBUG_SSA_PRINT
  // Print all after the headers: decl and code
  print_all_partition(std::cout);
# endif
}

/*******************************************************************\

 Function: prop_partitioning_target_equationt::convert_partition

 Inputs:

 Outputs:

 Purpose: Convert a specific partition of SSA steps

\*******************************************************************/
void prop_partitioning_target_equationt::convert_partition(prop_conv_solvert &prop_conv,
    interpolating_solvert &interpolator, partitiont& partition)
{
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
#   endif
    return;
  }
  // Convert the assumption propagation symbols
  partition_ifacet &partition_iface = partition.get_iface();
  partition_iface.callstart_literal =
          prop_conv.convert(partition_iface.callstart_symbol);
  partition_iface.callend_literal =
          prop_conv.convert(partition_iface.callend_symbol);
  if (partition_iface.assertion_in_subtree) {
    partition_iface.error_literal =
            prop_conv.convert(partition_iface.error_symbol);
  }
  if (partition.stub){
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
  partition.fle_part_id = interpolator.new_partition();

  // If this is a summary partition, apply the summary
  if (partition.summary) {
    convert_partition_summary(prop_conv, partition);
    // FIXME: Only use in the incremental solver mode (not yet implemented)
    // partition.processed = true;
    return;
  }

  // Reserve fresh variables for the partition boundary
  std::vector<symbol_exprt> common_symbs;
  fill_common_symbols(partition, common_symbs);
  prop_interpolantt::reserve_variables(prop_conv, common_symbs, partition.get_iface().common_symbols);
  // Convert the corresponding SSA steps
  convert_partition_guards(prop_conv, partition);
  convert_partition_assignments(prop_conv, partition);
  convert_partition_assumptions(prop_conv, partition);
 // if (partition.get_iface().function_id.c_str() == "c::main"){
 //   std::cout << "converting assertions\n";
    convert_partition_assertions(prop_conv, partition);
 // } else {
 //   std::cout << "skipping converting assertions\n";
 // }
  convert_partition_io(prop_conv, partition);
  convert_partition_goto_instructions(prop_conv, partition);
  // FIXME: Only use in the incremental solver mode (not yet implemented)
  // partition.processed = true;
}
/*******************************************************************\

Function: prop_partitioning_target_equationt::convert_partition_summary

  Inputs:

 Outputs:

 Purpose: Convert a summary partition (i.e., assert its summary)

\*******************************************************************/

void prop_partitioning_target_equationt::convert_partition_summary(
    prop_conv_solvert &prop_conv, partitiont& partition)
{
  std::vector<symbol_exprt> common_symbs;
  summary_storet* summary_store = summarization_context.get_summary_store();
  fill_common_symbols(partition, common_symbs);
  unsigned i = 0;

#   ifdef DEBUG_SSA
    std::cout << "Candidate summaries: " << partition.summaries->size() << std::endl;
#   endif

  bool is_recursive = partition.get_iface().summary_info.is_recursive(); //on_nondet();
  unsigned last_summary = partition.applicable_summaries.size() - 1;

  for (summary_ids_sett::const_iterator it =
          partition.applicable_summaries.begin();
          it != partition.applicable_summaries.end();
          ++it) {

    prop_summaryt& summary = dynamic_cast <prop_summaryt&> (summary_store->find_summary(*it));

    if (summary.is_valid() && (!is_recursive || last_summary == i++)){
#   ifdef DEBUG_SSA
      std::cout << "Substituting summary #" << *it << std::endl;
#   endif
      summary.substitute(prop_conv, common_symbs, partition.inverted_summary);
    }
  }
  
  summary_store = NULL;
}

/*******************************************************************\

Function: prop_partitioning_target_equationt::convert_partition_assignments

  Inputs:

 Outputs:

 Purpose: Convert a specific partition assignments of SSA steps

\*******************************************************************/

void prop_partitioning_target_equationt::convert_partition_assignments(
  prop_conv_solvert &prop_conv, partitiont& partition)
{
  for(SSA_stepst::const_iterator it = partition.start_it;
      it != partition.end_it; ++it)
  {
    if(it->is_assignment() && !it->ignore)
    {
#     ifdef DEBUG_SSA_PRINT
      exprt tmp(it->cond_expr);  
      //Print "ASSIGN-OUT:"
      expr_ssa_print(out_terms << "    " , tmp, partition_smt_decl, false);
      terms_counter++;
#     endif

      prop_conv.set_to_true(it->cond_expr);
    }
  }
}

/*******************************************************************\

Function: prop_partitioning_target_equationt::convert_partition_guards

  Inputs:

 Outputs:

 Purpose: Convert a specific partition guards of SSA steps

\*******************************************************************/

void prop_partitioning_target_equationt::convert_partition_guards(
  prop_conv_solvert &prop_conv, partitiont& partition)
{
  for(SSA_stepst::iterator it = partition.start_it;
      it != partition.end_it; ++it)
  {
    if(it->ignore)
      it->guard_literal=const_literal(false);
    else
    {
      it->guard_literal=prop_conv.convert(it->guard);
      
#     ifdef DEBUG_SSA_PRINT
      //Print "GUARD-OUT:"
      exprt tmp(it->guard);  
      expr_ssa_print_guard(out_terms, tmp, partition_smt_decl);
      if (!tmp.is_boolean())
      {
          terms_counter++; // SSA -> SMT shall be all in a new function
      }
#     endif
    }
  }
}

/*******************************************************************\

Function: prop_partitioning_target_equationt::convert_partition_assumptions

  Inputs:

 Outputs:

 Purpose: Convert a specific partition assumptions of SSA steps

\*******************************************************************/

void prop_partitioning_target_equationt::convert_partition_assumptions(
  prop_conv_solvert &prop_conv, partitiont& partition)
{
  for(SSA_stepst::iterator it = partition.start_it;
      it != partition.end_it; ++it)
  {
    if(it->is_assume())
    {
      if(it->ignore)
        it->cond_literal=const_literal(true);
      else
      {
        it->cond_literal=prop_conv.convert(it->cond_expr);
        
#	ifdef DEBUG_SSA_PRINT // Only for prop version!
        exprt tmp(it->cond_expr);  
        //Print "ASSUME-OUT:"
        expr_ssa_print(out_terms << "    " , tmp, partition_smt_decl, false);
        terms_counter++;
#       endif
      }
    }
  }
}

/*******************************************************************
 Function: prop_partitioning_target_equationt::convert_partition_goto_instructions

 Inputs:

 Outputs:

 Purpose: Convert a specific partition go-tos of SSA steps

 *  KE: added after the cprover upgrade
 \*******************************************************************/
void prop_partitioning_target_equationt::convert_partition_goto_instructions(
    prop_conv_solvert &prop_conv, partitiont& partition)
{
    for(SSA_stepst::iterator it = partition.start_it;
      it != partition.end_it; ++it)
    {
        if(it->is_goto())
        {
            if(it->ignore)
                it->cond_literal=const_literal(true);
            else
            {
                it->cond_literal=prop_conv.convert(it->cond_expr);
                
#           ifdef DEBUG_SSA_PRINT // Only for prop version!
                exprt tmp(it->cond_expr);
                //Print "GOTO-OUT:" -- Caused a bug with Global Vars. --
                expr_ssa_print(out_terms << "    " , tmp, partition_smt_decl, false);
                terms_counter++;
#           endif
            }           
        }
    }    
}

/*******************************************************************\

Function: prop_partitioning_target_equationt::convert_partition_assertions

  Inputs:

 Outputs:

 Purpose: Convert a specific partition assertions of SSA steps

\*******************************************************************/

void prop_partitioning_target_equationt::convert_partition_assertions(
  prop_conv_solvert &prop_conv, partitiont& partition)
{
    unsigned number_of_assertions = count_partition_assertions(partition); 
    unsigned number_of_assumptions = 0;
    const partition_ifacet& partition_iface = partition.get_iface();

    bvt bv;
    if (partition_iface.assertion_in_subtree) {
        bv.reserve(number_of_assertions + partition.child_ids.size());
    }

    literalt assumption_literal=const_literal(true);

    for (SSA_stepst::iterator it = partition.start_it;
    it != partition.end_it; ++it) {

    if ((it->is_assert()) && !(it->ignore))
    {

#     ifdef DEBUG_SSA_PRINT // Only for BV version
      //Print "ASSERT-OUT:"
      expr_ssa_print(out_terms << "    " , it->cond_expr, partition_smt_decl, true);
      terms_counter++;
#     endif

      // Collect ass \in assertions(f) in bv
      literalt tmp_literal = prop_conv.convert(it->cond_expr);
      it->cond_literal = prop_conv.prop.limplies(assumption_literal, tmp_literal);

      bv.push_back(!it->cond_literal);
    }
    else if (it->is_assume() && !it->ignore) {
      // If the assumption represents a call of the function g, 
      // encode callstart_g propagation formula:
      //
      // callstart_g <=>
      //     path_cond \land 
      //     (\land_{ass \in {assumptions(f)}} ass)
      //
      const partitiont* target_partition = find_target_partition(*it);

      if (target_partition && !target_partition->ignore) {
        const partition_ifacet& target_partition_iface = target_partition->get_iface();
        assert(!target_partition->invalid && !target_partition->processed);

        literalt tmp = prop_conv.prop.land(assumption_literal, it->guard_literal);
        prop_conv.prop.set_equal(tmp, target_partition_iface.callstart_literal);
      
        #ifdef DEBUG_SSA_PRINT // Print of assert
        terms_counter++;
	std::ostream out_temp2(0); std::stringbuf temp2_buf; out_temp2.rdbuf(&temp2_buf); // Pre-order printing
	int assume_counter=0;
        expr_ssa_print(out_temp2 << "    (= ", target_partition_iface.callstart_symbol, partition_smt_decl, false);
        for (SSA_stepst::iterator it2 = partition.start_it; it2 != it; ++it2) {
          if (it2->is_assume() && !it2->ignore) {
            assume_counter++;
            expr_ssa_print(out_temp2 << "        ", it2->cond_expr, partition_smt_decl, false);
          }
        }
        // If there are more than one term - add and
        switch (assume_counter) {
            case 0: out_terms << temp2_buf.str() << "        true\n" << "    )\n"; break; // Shall be called only once at the beginning of the code
            case 1: out_terms << temp2_buf.str() << "    )\n"; break;
            default: out_terms << "    (and \n  " << temp2_buf.str() << "      )\n" << "    )\n"; break;
        }
        #endif
      }
      
      // Collect this assumption as:
      //
      //     assumption_literal = \land_{ass \in assumptions(f)} ass
      //
      assumption_literal = prop_conv.prop.land(assumption_literal, it->cond_literal);
      number_of_assumptions++;
    } 
  }
  
  for (partition_idst::const_iterator it = partition.child_ids.begin();
          it != partition.child_ids.end(); ++it) {
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
    
    if (partition.parent_id == partitiont::NO_PARTITION && !upgrade_checking) 
    {
      prop_conv.prop.lcnf(bv);
      
      #ifdef DEBUG_SSA_PRINT // Root Encoding

      // Pre-order printing
      std::ostream out_temp1(0);
      std::stringbuf temp1_buf;
      out_temp1.rdbuf(&temp1_buf);

      int assert_counter=0;

      for (SSA_stepst::iterator it = partition.start_it; it != partition.end_it; ++it) {
        if (it->is_assert() && !it->ignore) {
          assert_counter++;
          if (assert_counter == 1)
            expr_ssa_print(out_temp1, it->cond_expr, partition_smt_decl, false);
          else
	    expr_ssa_print(out_temp1 << "        ", it->cond_expr, partition_smt_decl, false);
        }
      }
      for (partition_idst::const_iterator it = partition.child_ids.begin(); 
              it != partition.child_ids.end();
              ++it) {
        const partitiont& target_partition = partitions[*it];
        const partition_ifacet& target_partition_iface = target_partition.get_iface();

        if (!target_partition.ignore && 
                target_partition_iface.assertion_in_subtree) {
          assert_counter++;
          if (assert_counter == 1)
            expr_ssa_print(out_temp1, target_partition_iface.error_symbol, partition_smt_decl, false);
          else
            expr_ssa_print(out_temp1 << "        ", target_partition_iface.error_symbol, partition_smt_decl, false);
        }
      }
      if (assert_counter > 0) {
    	  terms_counter++;
    	  if (assert_counter == 1) 
              out_terms << "    " << temp1_buf.str().substr(4);
    	  else 
              out_terms << "    (or \n      (" << temp1_buf.str() << "      )\n" << "    )\n";
      }
      #endif
    } 
    else 
    {
      literalt tmp = prop_conv.prop.lor(bv);
      prop_conv.prop.set_equal(tmp, partition_iface.error_literal);
      
      #ifdef DEBUG_SSA_PRINT // XXX Encoding error_f: ",
      terms_counter++;
      expr_ssa_print(out_terms << "    (= ",
              partition_iface.error_symbol, partition_smt_decl, false);
      std::ostream out_temp_assert(0); std::stringbuf temp_assert_buf; out_temp_assert.rdbuf(&temp_assert_buf); // Pre-order printing
      int assert_counter=0;
      for (SSA_stepst::iterator it = partition.start_it; it != partition.end_it; ++it) {
        if (it->is_assert() && !it->ignore) {
          assert_counter++;
          expr_ssa_print(out_temp_assert << "          ", it->cond_expr, partition_smt_decl, false);
        }
      }
      for (partition_idst::const_iterator it = partition.child_ids.begin(); 
              it != partition.child_ids.end();
              ++it) {
        const partitiont& target_partition = partitions[*it];
        const partition_ifacet& target_partition_iface = target_partition.get_iface();

        if (!target_partition.ignore && 
                target_partition_iface.assertion_in_subtree) {
        	assert_counter++;
        	expr_ssa_print(out_temp_assert << "          ", target_partition_iface.error_symbol,partition_smt_decl, false);
        }
      }
      std::ostream out_temp_assume(0); std::stringbuf temp_assume_buf; out_temp_assume.rdbuf(&temp_assume_buf); // Pre-order printing
	  int assume_counter=0;
	  for (symex_target_equationt::SSA_stepst::iterator it2 = partition.start_it; it2 != partition.end_it; ++it2) {
		  if (it2->is_assume() && !it2->ignore) {
			  assume_counter++;
			  expr_ssa_print(out_temp_assume << "            ", it2->cond_expr, partition_smt_decl, false);
		  }
	  }
	  std::string assume_code ="";
      if (assume_counter > 1) assume_code = "          (and \n" + temp_assume_buf.str() + "          )\n";
      else assume_code = temp_assume_buf.str();
      if (assert_counter > 0) {
    	  terms_counter++;
    	  if (assert_counter == 1) out_terms << "      (not\n        (=>\n" << assume_code << temp_assert_buf.str() << "        )\n      )\n    )\n";
    	  else out_terms << "      (not\n        (=>\n" << assume_code << "          (or \n  " << temp_assert_buf.str() << "          )\n        )\n      )\n    )\n";
      }
      #endif
    }
    
  }

//  // Emit error_root = true for the ROOT partition
//  if (partition.parent_id == partitiont::NO_PARTITION) {
//    prop_conv.prop.l_set_to_true(partition_iface.error_literal);
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
    literalt tmp = prop_conv.prop.limplies(partition_iface.callend_literal,
            assumption_literal);
    prop_conv.prop.l_set_to_true(tmp);

#   ifdef DEBUG_SSA_PRINT // "XXX Call END implication: \n";
    terms_counter++;
    expr_ssa_print(out_terms << "    (=> ", partition_iface.callend_symbol, partition_smt_decl, false, true);
	std::ostream out_temp(0); std::stringbuf temp_buf; out_temp.rdbuf(&temp_buf); // Pre-order printing
    int assume_counter=0;
	for (symex_target_equationt::SSA_stepst::iterator it2 = partition.start_it; it2 != partition.end_it; ++it2) {
	  if (it2->is_assume() && !it2->ignore) {
		if (assume_counter == 0 && isFirstCallExpr(it2->cond_expr)) {assume_counter++; expr_ssa_print(out_temp << "        ", it2->guard, partition_smt_decl, false);}
		assume_counter++; expr_ssa_print(out_temp << "        ", it2->cond_expr, partition_smt_decl, false);
	  }
	}
    if (assume_counter > 1) out_terms << "\n      (and \n" << temp_buf.str() << "      )\n" << "    )\n";
    else out_terms << "\n" << temp_buf.str() << "    )\n";
#   endif
  }
}

/*******************************************************************\

Function: prop_partitioning_target_equationt::convert_partition_io

  Inputs:

 Outputs:

 Purpose: Convert a specific partition io of SSA steps

\*******************************************************************/

void prop_partitioning_target_equationt::convert_partition_io(
  prop_conv_solvert &prop_conv, partitiont& partition)
{
  for(SSA_stepst::iterator it = partition.start_it;
      it != partition.end_it; ++it)
    if(!it->ignore)
    {
      for(std::list<exprt>::const_iterator
          o_it=it->io_args.begin();
          o_it!=it->io_args.end();
          ++o_it)
      {
        exprt tmp=*o_it;
        if(tmp.is_constant() ||
           tmp.id()==ID_string_constant)
          it->converted_io_args.push_back(tmp);
        else
        {
          symbol_exprt symbol(("symex::io::"+std::to_string(io_count_global++)), tmp.type());
          prop_conv.set_to(equal_exprt(tmp, symbol), true);
          it->converted_io_args.push_back(symbol);
        }
      }
    }
}

/*******************************************************************\

Function: prop_partitioning_target_equationt::extract_interpolants

  Inputs:

 Outputs:

 Purpose: Extract interpolants corresponding to the created partitions

\*******************************************************************/
void prop_partitioning_target_equationt::extract_interpolants(
  interpolating_solvert& interpolator, const prop_conv_solvert& decider,
  interpolant_mapt& interpolant_map)
{
#ifdef PRODUCE_PROOF     
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
              partition.applicable_summaries.begin();
              it != partition.applicable_summaries.end(); ++it) {
        partition.get_iface().summary_info.add_used_summary(*it);
      }
    }
    
    if (!partition.is_inline() ||
            (partition.get_iface().assertion_in_subtree && !store_summaries_with_assertion) ||
        partition.get_iface().summary_info.is_recursion_nondet()
    )
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
    
    if (!partition.is_inline() ||
            (ipartition.assertion_in_subtree &&
                !store_summaries_with_assertion)
      || partition.get_iface().summary_info.is_recursion_nondet()
            )
      continue;
    fill_partition_ids(pid, itp_task[tid++]);
  }

  // Interpolate...
  interpolantst itp_result;
  itp_result.reserve(valid_tasks);
  interpolator.get_interpolant(itp_task, itp_result);

  // Interpret the result
  std::vector<symbol_exprt> common_symbs;
  interpolant_map.reserve(valid_tasks);
  for (unsigned pid = 1, tid = 0; pid < partitions.size(); ++pid) {
    partitiont& partition = partitions[pid];

    if (!partition.is_inline() ||
            (partition.get_iface().assertion_in_subtree && !store_summaries_with_assertion)
            || partition.get_iface().summary_info.is_recursion_nondet()
    )
      continue;

    prop_itpt* itp = dynamic_cast <prop_itpt*> (itp_result[tid]);

    tid++;

    if (itp->is_trivial()) {
      std::cout << "Interpolant for function: " <<
                partition.get_iface().function_id.c_str() << " is trivial." << std::endl;
      continue;
    }

    if (partition.get_iface().summary_info.is_recursion_nondet()){
      std::cout << "Skip interpolants for nested recursion calls." << std::endl;
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

    itp->generalize(decider, common_symbs);

    if (itp->is_trivial()) {
      continue;
    }

    // Store the interpolant
    summary_idt summary_id = summary_store->insert_summary(*itp);

    interpolant_map.push_back(interpolant_mapt::value_type(
      &partition.get_iface(), summary_id));
  }
  
  summary_store = NULL;
#else
  assert(0);
#endif
}

/*******************************************************************\

Function: prop_partitioning_target_equationt::fill_partition_ids

  Inputs:

 Outputs:

 Purpose: Fill in ids of all the child partitions

\*******************************************************************/
void prop_partitioning_target_equationt::fill_partition_ids(
  partition_idt partition_id, fle_part_idst& part_ids)
{

  partitiont& partition = partitions[partition_id];

  if (partition.stub){
    return;
  }

  assert(!partition.invalid &&
          (!partition.get_iface().assertion_in_subtree || store_summaries_with_assertion));

  if (partition.ignore) {
    assert(partition.child_ids.empty());
    return;
  }

  // Current partition id
  part_ids.push_back(partition.fle_part_id);

  assert(partition.is_inline() || partition.child_ids.empty());

  // Child partition ids
  for (partition_idst::iterator it = partition.child_ids.begin()++;
          it != partition.child_ids.end(); ++it) {
    fill_partition_ids(*it, part_ids);
  }
}
