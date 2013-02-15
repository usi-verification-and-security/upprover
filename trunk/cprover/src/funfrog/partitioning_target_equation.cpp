/*******************************************************************\

Module: Symex target equation which tracks different partitions for
different deferred functions. Based on symex_target_equation.cpp.

Author: Ondrej Sery

\*******************************************************************/

#include <i2string.h>
#include <std_expr.h>

#include "partitioning_target_equation.h"
#include "expr_pretty_print.h"
#include "solvers/sat/cnf.h"

//#define DEBUG_SSA
//#define DEBUG_ITP
//#define DEBUG_ENCODING
#include "solvers/satcheck_opensmt.h"

/*******************************************************************\

 Function: partitioning_target_equationt::convert

 Inputs:

 Outputs:

 Purpose: Convert all the SSA steps into the corresponding formulas in
 the corresponding partitions

\*******************************************************************/
void partitioning_target_equationt::convert(prop_convt &prop_conv, 
          interpolating_solvert &interpolator)
{
  int part_id = partitions.size();
  for (partitionst::reverse_iterator it = partitions.rbegin();
          it != partitions.rend(); ++it) {
//#   ifdef DEBUG_SSA
    std::cout << "XXX" << std::string(77, '=') << std::endl;
    unsigned vars_before = prop_conv.prop.no_variables();
    unsigned clauses_before = dynamic_cast<cnf_solvert&>(prop_conv.prop).no_clauses();
    std::cout << "XXX Partition: " << --part_id <<
            " (ass_in_subtree: " << it->get_iface().assertion_in_subtree << ")" << 
            " - " << it->get_iface().function_id.c_str() <<
            " (loc: " << it->get_iface().summary_info.get_call_location() << ", " <<
            ((it->summary) ? ((it->inverted_summary) ? "INV" : "SUM") :
                ((it->stub) ? "TRU" : "INL")) << ")" <<
            std::endl;
//#   endif
    convert_partition(prop_conv, interpolator, *it);
#   ifdef DEBUG_ENCODING
    unsigned vars_after = prop_conv.prop.no_variables();
    unsigned clauses_after = dynamic_cast<cnf_solvert&>(prop_conv.prop).no_clauses();
    it->clauses = clauses_after - clauses_before;
    it->vars = vars_after - vars_before;
    std::cout << "    vars: " << it->vars << std::endl <<
            "    clauses: " << it->clauses << std::endl;
    std::cout << "    last_var: " << dynamic_cast<satcheck_opensmtt&>(prop_conv.prop).get_last_var() << std::endl;

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
}

/*******************************************************************\

 Function: partitioning_target_equationt::convert_partition

 Inputs:

 Outputs:

 Purpose: Convert a specific partition of SSA steps

\*******************************************************************/
void partitioning_target_equationt::convert_partition(prop_convt &prop_conv, 
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
#	endif
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
  interpolantt::reserve_variables(prop_conv, common_symbs, partition.get_iface().common_symbols);

  // Convert the corresponding SSA steps
  convert_partition_guards(prop_conv, partition);
  convert_partition_assignments(prop_conv, partition);
  convert_partition_assumptions(prop_conv, partition);
  convert_partition_assertions(prop_conv, partition);
  convert_partition_io(prop_conv, partition);
  // FIXME: Only use in the incremental solver mode (not yet implemented)
  // partition.processed = true;
}
/*******************************************************************\

Function: partitioning_target_equationt::convert_partition_summary

  Inputs:

 Outputs:

 Purpose: Convert a summary partition (i.e., assert its summary)

\*******************************************************************/

void partitioning_target_equationt::convert_partition_summary(
    prop_convt &prop_conv, partitiont& partition)
{
  std::vector<symbol_exprt> common_symbs;
  summary_storet& summary_store = summarization_context.get_summary_store();
  fill_common_symbols(partition, common_symbs);

#   ifdef DEBUG_SSA
    std::cout << "Candidate summaries: " << partition.summaries->size() << std::endl;
#   endif
  for (summary_ids_sett::const_iterator it = 
          partition.applicable_summaries.begin();
          it != partition.applicable_summaries.end();
          ++it) {
#   ifdef DEBUG_SSA
    std::cout << "Substituting summary #" << *it << std::endl;
#   endif
    summaryt& summary = summary_store.find_summary(*it);
    if (summary.is_valid()){
      summary.substitute(prop_conv, common_symbs, partition.inverted_summary);
    }
  }
}

/*******************************************************************\

Function: partitioning_target_equationt::convert_partition_assignments

  Inputs:

 Outputs:

 Purpose: Convert a specific partition assignments of SSA steps

\*******************************************************************/

void partitioning_target_equationt::convert_partition_assignments(
  prop_convt &prop_conv, partitiont& partition) const
{
  for(SSA_stepst::const_iterator it = partition.start_it;
      it != partition.end_it; ++it)
  {
    if(it->is_assignment() && !it->ignore)
    {
      exprt tmp(it->cond_expr);

#     ifdef DEBUG_SSA      
      expr_pretty_print(std::cout << "ASSIGN-OUT:" << std::endl, tmp, 2);
#     endif

      prop_conv.set_to_true(tmp);
    }
  }
}

/*******************************************************************\

Function: partitioning_target_equationt::convert_partition_guards

  Inputs:

 Outputs:

 Purpose: Convert a specific partition guards of SSA steps

\*******************************************************************/

void partitioning_target_equationt::convert_partition_guards(
  prop_convt &prop_conv, partitiont& partition)
{
  for(SSA_stepst::iterator it = partition.start_it;
      it != partition.end_it; ++it)
  {
    if(it->ignore)
      it->guard_literal=const_literal(false);
    else
    {
      exprt tmp(it->guard_expr);

#     ifdef DEBUG_SSA      
      expr_pretty_print(std::cout << "GUARD-OUT:" << std::endl, tmp, 2);
#     endif

      it->guard_literal=prop_conv.convert(tmp);
    }
  }
}

/*******************************************************************\

Function: partitioning_target_equationt::convert_partition_assumptions

  Inputs:

 Outputs:

 Purpose: Convert a specific partition assumptions of SSA steps

\*******************************************************************/

void partitioning_target_equationt::convert_partition_assumptions(
  prop_convt &prop_conv, partitiont& partition)
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
        exprt tmp(it->cond_expr);

#       ifdef DEBUG_SSA      
        expr_pretty_print(std::cout << "ASSUME-OUT:" << std::endl, tmp, 2);
#       endif

        it->cond_literal=prop_conv.convert(tmp);
      }
    }
  }
}

/*******************************************************************\

Function: partitioning_target_equationt::convert_partition_assertions

  Inputs:

 Outputs:

 Purpose: Convert a specific partition assertions of SSA steps

\*******************************************************************/

void partitioning_target_equationt::convert_partition_assertions(
  prop_convt &prop_conv, partitiont& partition)
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
    if (it->is_assert())
    {

#     ifdef DEBUG_SSA      
      expr_pretty_print(std::cout << "ASSERT-OUT:" << std::endl, it->cond_expr);
#     endif

      // Collect ass \in assertions(f) in bv
      literalt tmp_literal = prop_conv.convert(it->cond_expr);
      it->cond_literal = prop_conv.prop.limplies(assumption_literal, tmp_literal);

      bv.push_back(prop_conv.prop.lnot(it->cond_literal));
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
        
        #ifdef DEBUG_SSA      
        expr_pretty_print(std::cout << "XXX Call START equality: ",
                target_partition_iface.callstart_symbol);
        expr_pretty_print(std::cout << "  = ", it->guard_expr);
        for (SSA_stepst::iterator it2 = partition.start_it; it2 != it; ++it2) {
          if (it2->is_assume() && !it2->ignore) {
            expr_pretty_print(std::cout << "  & ", it2->cond_expr);
          }
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
      
      #ifdef DEBUG_SSA
      std::cout << "XXX Encoding error in ROOT: " << std::endl;
      for (SSA_stepst::iterator it = partition.start_it; it != partition.end_it; ++it) {
        if (it->is_assert() && !it->ignore) {
          expr_pretty_print(std::cout << "  | ", it->cond_expr);
        }
      }
      for (partition_idst::const_iterator it = partition.child_ids.begin(); 
              it != partition.child_ids.end();
              ++it) {
        const partitiont& target_partition = partitions[*it];
        const partition_ifacet& target_partition_iface = target_partition.get_iface();

        if (!target_partition.ignore && 
                target_partition_iface.assertion_in_subtree) {
          expr_pretty_print(std::cout << "  | ", target_partition_iface.error_symbol);
        }
      }
      #endif
    } 
    else 
    {
      literalt tmp = prop_conv.prop.lor(bv);
      prop_conv.prop.set_equal(tmp, partition_iface.error_literal);
      
      #ifdef DEBUG_SSA
      expr_pretty_print(std::cout << "XXX Encoding error_f: ",
              partition_iface.error_symbol);
      for (SSA_stepst::iterator it = partition.start_it; it != partition.end_it; ++it) {
        if (it->is_assert() && !it->ignore) {
          expr_pretty_print(std::cout << "  | ", it->cond_expr);
        }
      }
      for (partition_idst::const_iterator it = partition.child_ids.begin(); 
              it != partition.child_ids.end();
              ++it) {
        const partitiont& target_partition = partitions[*it];
        const partition_ifacet& target_partition_iface = target_partition.get_iface();

        if (!target_partition.ignore && 
                target_partition_iface.assertion_in_subtree) {
          expr_pretty_print(std::cout << "  | ", target_partition_iface.error_symbol);
        }
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

#   ifdef DEBUG_SSA      
    expr_pretty_print(std::cout << "XXX Call END implication: ", partition_iface.callend_symbol);
    for (SSA_stepst::iterator it2 = partition.start_it; it2 != partition.end_it; ++it2) {
      if (it2->is_assume()) {
        expr_pretty_print(std::cout << "  => ", it2->cond_expr);
      }
    }
#   endif
  }
}

/*******************************************************************\

Function: partitioning_target_equationt::convert_partition_io

  Inputs:

 Outputs:

 Purpose: Convert a specific partition io of SSA steps

\*******************************************************************/

void partitioning_target_equationt::convert_partition_io(
  prop_convt &prop_conv, partitiont& partition)
{
  unsigned io_count=0;

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
          symbol_exprt symbol;
          symbol.type()=tmp.type();
          symbol.set_identifier("symex::io::"+i2string(io_count++));
          prop_conv.set_to(equality_exprt(tmp, symbol), true);
          it->converted_io_args.push_back(symbol);
        }
      }
    }
}

/*******************************************************************\

Function: partitioning_target_equationt::partitioning_target_equationt

  Inputs:

 Outputs:

 Purpose: Collects information about the specified partitions for later
 processing and conversion

\*******************************************************************/

void partitioning_target_equationt::prepare_partitions()
{
  // Fill in the partition start and end iterator for easier access during
  // the conversion process
  unsigned idx = 0;
  SSA_stepst::iterator ssa_it = SSA_steps.begin();

  // The last partition has an undefined end, fix it!
  if (!partitions.empty()) {
    partitions[current_partition_id].end_idx = SSA_steps.size();
  }

  for (partitionst::iterator it = partitions.begin();
          it != partitions.end(); ++it) {

    assert(it->filled);
    bool ignore = true;

    it->start_it = ssa_it;

#   ifdef DEBUG_SSA
    std::cout << "Partition SSA indices: " << idx << ", " << 
            it->start_idx << ", " << it->end_idx << 
            " size: " << partitions.size() << std::endl;
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

/*******************************************************************\

Function: partitioning_target_equationt::prepare_SSA_exec_order_rec

  Inputs:

 Outputs:

 Purpose: Fills in the SSA_steps_exec_order holding pointers to SSA steps 
 ordered in the order of program execution (i.e., as they would be normally 
 ordered in symex_target_equation).

\*******************************************************************/
void partitioning_target_equationt::prepare_SSA_exec_order(
        const partitiont& partition)
{
  partition_locst::const_iterator loc_it = partition.child_locs.begin();
  partition_idst::const_iterator id_it = partition.child_ids.begin();
  unsigned SSA_idx = partition.start_idx;
  
  for(SSA_stepst::iterator it = partition.start_it;
      it != partition.end_it; ++it, ++SSA_idx)
  {
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

/*******************************************************************\

Function: partitioning_target_equationt::find_target_partition

  Inputs:

 Outputs:

 Purpose: Find partition corresponding to the function call. 
 If the given SSA step is a callend assumption, the corresponding target 
 partition is returned. If not, NULL is returned.

\*******************************************************************/
const partitiont* partitioning_target_equationt::find_target_partition(
  const SSA_stept& step) 
{
  if (step.cond_expr.id() == ID_symbol ||
          (step.cond_expr.id() == ID_implies && step.cond_expr.op1().id() == ID_symbol)) {
    irep_idt id = step.cond_expr.id() == ID_symbol ?
            step.cond_expr.get(ID_identifier) :
            step.cond_expr.op1().get(ID_identifier);
    partition_mapt::iterator pit =
            partition_map.find(id);

    if (pit != partition_map.end()) {
      return &partitions[pit->second];
    }
  }
  return NULL;
}

/*******************************************************************\

Function: partitioning_target_equationt::extract_interpolants

  Inputs:

 Outputs:

 Purpose: Extract interpolants corresponding to the created partitions

\*******************************************************************/
void partitioning_target_equationt::extract_interpolants(
  interpolating_solvert& interpolator, const prop_convt& decider,
  interpolant_mapt& interpolant_map, bool tree_interpolants, double reduction_timeout)
{
  // Prepare the interpolation task. NOTE: ignore the root partition!
  unsigned valid_tasks = 0;
  summary_storet& summary_store = summarization_context.get_summary_store();

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
            (partition.get_iface().assertion_in_subtree && !store_summaries_with_assertion))
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
            (ipartition.assertion_in_subtree && !store_summaries_with_assertion))
      continue;
    fill_partition_ids(pid, itp_task[tid++]);

    //coloring staff
    if (coloring_mode != NO_COLORING){
      if (coloring_mode == COLORING_FROM_FILE){
        // serialize to separate files
        std::string filename = "__common_";
        filename.append(ipartition.function_id.as_string());
        filename.append("_");
        filename.append(i2string(pid));
        if (!ipartition.deserialize_common(filename)){
          ipartition.serialize_common(filename);
          ipartition.distribute_A_B();
        }
      } else if (coloring_mode == RANDOM_COLORING){
        ipartition.distribute_A_B();
      }
      interpolator.addAB(ipartition.A_vars, ipartition.B_vars, ipartition.AB_vars);
    }
  }

  // Interpolate...
  interpolantst itp_result;
  itp_result.reserve(valid_tasks);

  if (tree_interpolants){
    opensmt::InterpolationTree *itp_tree = fill_partition_tree(*partitions.begin());
    interpolator.get_interpolant(itp_tree, itp_task, itp_result);
  } else {
    interpolator.get_interpolant(itp_task, itp_result, reduction_timeout);
  }

  // Interpret the result
  std::vector<symbol_exprt> common_symbs;
  interpolant_map.reserve(valid_tasks);
  for (unsigned pid = 1, tid = 0; pid < partitions.size(); ++pid) {
    partitiont& partition = partitions[pid];

    if (!partition.is_inline() ||
            (partition.get_iface().assertion_in_subtree && !store_summaries_with_assertion))
      continue;
    
    interpolantt& itp = itp_result[tid++];

    if (itp.is_trivial()) {
#     ifdef DEBUG_ITP
      std::cout << "Trivial interpolant." << std::endl;
#     endif
      continue;
    }

//    if (partition.get_iface().summary_info.is_recursion_nondet()){
//      std::cout << "Skip interpolants for nested recursion calls." << std::endl;
//      continue;
//    }
    
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
    
    itp.generalize(decider, common_symbs);

    // Store the interpolant
    summary_idt summary_id = summary_store.insert_summary(itp);
    
    interpolant_map.push_back(interpolant_mapt::value_type(
      &partition.get_iface(), summary_id));
  }
}

/*******************************************************************\

Function: partitioning_target_equationt::fill_partition_ids

  Inputs:

 Outputs:

 Purpose: Fill in ids of all the child partitions

\*******************************************************************/
void partitioning_target_equationt::fill_partition_ids(
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

/*******************************************************************\

Function: partitioning_target_equationt::fill_partition_tree

  Inputs:

 Outputs:

 Purpose: Fill a tree from all the child partitions

\*******************************************************************/
opensmt::InterpolationTree* partitioning_target_equationt::fill_partition_tree(
    partitiont& partition)
{
  opensmt::InterpolationTree* itp_tree;
  itp_tree = new opensmt::InterpolationTree(partition.fle_part_id, partition.fle_part_id); //ToDo: what is nodeId?

  // Child partition ids
  for (partition_idst::iterator it = partition.child_ids.begin()++;
          it != partition.child_ids.end(); ++it) {
    partitiont& partition = partitions[*it];
    if (!partition.invalid){
      opensmt::InterpolationTree* child_tree = fill_partition_tree(partition);
      (*itp_tree).addChild(child_tree);
    }
  }

  return itp_tree;
}
