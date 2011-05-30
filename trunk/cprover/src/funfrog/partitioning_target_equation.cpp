/*******************************************************************\

Module: Symex target equation which tracks different partitions for
different deferred functions. Based on symex_target_equation.cpp.

Author: Ondrej Sery

\*******************************************************************/

#include <i2string.h>
#include <std_expr.h>

#include "partitioning_target_equation.h"
#include "expr_pretty_print.h"

//#define DEBUG_SSA
//#define DEBUG_ITP

/*******************************************************************\

 Function: partitioning_target_equationt::convert

 Inputs:

 Outputs:

 Purpose: Convert all the SSA steps into the corresponding formulas in
 the corresponding partitions

\*******************************************************************/
void partitioning_target_equationt::convert(
  prop_convt &prop_conv, interpolating_solvert &interpolator)
{
  int part_id = partitions.size();
  for (partitionst::reverse_iterator it = partitions.rbegin();
          it != partitions.rend(); ++it) {
    std::cout << "XXX Partition: " << --part_id << std::endl;
    convert_partition(prop_conv, interpolator, *it);
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
    if (partition.ignore)
      std::cout << "  partition sliced out." << std::endl;
    else if (partition.processed)
      std::cout << "  partition already processed." << std::endl;
    else
      std::cout << "  partition invalidated (refined)." << std::endl;
    return;
  }
  
  // Tell the interpolator about the new partition.
  partition.fle_part_id = interpolator.new_partition();

  // Convert the assumption propagation symbols
  partition_ifacet &partition_iface = partition.get_iface();
  partition_iface.callstart_literal = 
          prop_conv.convert(partition_iface.callstart_symbol);
  partition_iface.callend_literal = 
          prop_conv.convert(partition_iface.callend_symbol);

  // If this is a summary partition, apply the summary
  if (partition.is_summary) {
    convert_partition_summary(prop_conv, partition);
    // FIXME: Only use in the incremental solver mode (not yet implemented)
    // partition.processed = true;
    return;
  }

  // Reserve fresh variables for the partition boundary
  std::vector<symbol_exprt> common_symbs;
  fill_common_symbols(partition, common_symbs);
  interpolantt::reserve_variables(prop_conv, common_symbs);
          
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
  fill_common_symbols(partition, common_symbs);

#   ifdef DEBUG_SSA      
    std::cout << "Candidate summaries: " << partition.summaries->size() << std::endl;
#   endif
  for (hash_set_cont<unsigned>::const_iterator it = 
          partition.applicable_summaries.begin();
          it != partition.applicable_summaries.end();
          ++it) {
#   ifdef DEBUG_SSA      
    std::cout << "Substituting summary #" << *it << std::endl;
#   endif
    partition.summaries->at(*it).substitute(prop_conv, common_symbs);
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
# if 0
  // FIXME: This is unsound since also assumptions in the partitions without
  // any assertions may be important.
  if(number_of_assertions==0)
    return;

  // we find out if there is only _one_ assertion,
  // which allows for a simpler formula

  if(number_of_assertions==1)
  {
    // FIXME: Without slicing, this is unsound, since some subsequent,
    // but unsilced, assumptions may hide the assertion violation.
    for(SSA_stepst::iterator it = partition.start_it;
        it != partition.end_it; ++it)
      if(it->is_assert())
      {
        prop_conv.set_to_false(it->cond_expr);

        expr_pretty_print(std::cout << "ASSERT-OUT:" << std::endl, it->cond_expr, 2);

        it->cond_literal=prop_conv.convert(it->cond_expr);
        return; // prevent further assumptions!
      }
      else if(it->is_assume())
        prop_conv.set_to_true(it->cond_expr);

    assert(false); // unreachable
  }
# endif

  bvt bv;

  bv.reserve(number_of_assertions);

  literalt assumption_literal=const_literal(true);

  for (SSA_stepst::iterator it = partition.start_it;
      it != partition.end_it; ++it) {
    if (it->is_assert())
    {

#     ifdef DEBUG_SSA      
      expr_pretty_print(std::cout << "ASSERT-OUT:" << std::endl, it->cond_expr, 2);
#     endif

      // do the expression
      literalt tmp_literal=prop_conv.convert(it->cond_expr);

      it->cond_literal=prop_conv.prop.limplies(assumption_literal, tmp_literal);

      bv.push_back(prop_conv.prop.lnot(it->cond_literal));
    }
    else if (it->is_assume() && !it->ignore) {
      // If it is a call end symbol, we need to emit the assumption propagation
      // formula for the given callsite.
      if (number_of_assumptions > 0 && it->cond_expr.id() == ID_symbol) {
        partition_mapt::iterator pit =
                partition_map.find(it->cond_expr.get(ID_identifier));

        if (pit != partition_map.end()) {
          partitiont& target_partition = partitions[pit->second];
          // Emit the assumption propagation formula
          literalt tmp = prop_conv.prop.limplies(
                  target_partition.get_iface().callstart_literal,
                  assumption_literal);

          prop_conv.prop.l_set_to_true(tmp);

#         ifdef DEBUG_SSA      
          expr_pretty_print(std::cout << "XXX Call START implication: ",
                  target_partition.callstart_symbol);
          for (SSA_stepst::iterator it2 = partition.start_it; it2 != it; ++it2) {
            if (it2->is_assume() && !it2->ignore) {
              expr_pretty_print(std::cout << "  => ", it2->cond_expr);
            }
          }
#         endif
        }
      }

      // Collect this assumption
      assumption_literal=
        prop_conv.prop.land(assumption_literal, it->cond_literal);
      number_of_assumptions++;
    }
  }

  // Assert the collected assertions
  if (!bv.empty())
    prop_conv.prop.lcnf(bv);

  if (partition.parent_id != partitiont::NO_PARTITION && number_of_assumptions > 0) {
    // Assert the assumption propagation formula for the partition
    literalt tmp = prop_conv.prop.limplies(
            partition.get_iface().callend_literal,
            assumption_literal);

#   ifdef DEBUG_SSA      
    expr_pretty_print(std::cout << "XXX Call END implication: ", partition.callend_symbol);
    for (SSA_stepst::iterator it2 = partition.start_it; it2 != partition.end_it; ++it2) {
      if (it2->is_assume()) {
        expr_pretty_print(std::cout << "  => ", it2->cond_expr);
      }
    }
#   endif

    prop_conv.prop.l_set_to_true(tmp);
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

    if (it->is_summary)
      continue;

    while (idx != it->end_idx) {
      assert(ssa_it != SSA_steps.end());
      ignore &= ssa_it->ignore;
      ++ssa_it;
      ++idx;
    }
    it->end_it = ssa_it;
    it->ignore = ignore;
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
      
      if (!partition.is_summary)
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

    if (!partition.is_summary)
      prepare_SSA_exec_order(partition);

    ++loc_it;
    ++id_it;
  }
}

/*******************************************************************\

Function: partitioning_target_equationt::extract_interpolants

  Inputs:

 Outputs:

 Purpose: Extract interpolants corresponding to the created partitions

\*******************************************************************/
void partitioning_target_equationt::extract_interpolants(
  interpolating_solvert& interpolator, const prop_convt& decider,
  interpolant_mapt& interpolant_map, double reduction_timeout)
{
  // Prepare the interpolation task. NOTE: ignore the root partition!
  unsigned valid_tasks = 0;

  for (unsigned i = 1; i < partitions.size(); ++i) {
    if (partitions[i].is_summary || partitions[i].ignore)
      continue;
    
    valid_tasks++;
  }

  interpolation_taskt itp_task(valid_tasks);

  for (unsigned pid = 1, tid = 0; pid < partitions.size(); ++pid) {
    if (partitions[pid].is_summary || partitions[pid].ignore)
      continue;
    fill_partition_ids(pid, itp_task[tid++]);
  }

  // Interpolate...
  interpolantst itp_result;
  itp_result.reserve(valid_tasks);
  interpolator.get_interpolant(itp_task, itp_result, reduction_timeout);

  // Interpret the result
  std::vector<symbol_exprt> common_symbs;
  interpolant_map.reserve(valid_tasks);
  for (unsigned pid = 1, tid = 0; pid < partitions.size(); ++pid) {
    if (partitions[pid].is_summary || partitions[pid].ignore)
      continue;
    // Store the interpolant
    partitiont& partition = partitions[pid];
    interpolant_map.push_back(interpolant_mapt::value_type(
      partition.get_iface().function_id, interpolantst::value_type()));
    interpolantst::reference interpolant = interpolant_map.back().second;
    interpolant.swap(itp_result[tid++]);

    // Generalize the interpolant
    fill_common_symbols(partition, common_symbs);

#   ifdef DEBUG_ITP
    std::cout << "Common symbols (" << common_symbs.size() << "):" << std::endl;
    for (std::vector<symbol_exprt>::iterator it = common_symbs.begin();
            it != common_symbs.end(); ++it)
      std::cout << it->get_identifier() << std::endl;

    std::cout << "Generalizing interpolant" << std::endl;
#   endif
    interpolant.generalize(decider, common_symbs);
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

  // Current partition id
  part_ids.push_back(partition.fle_part_id);

  // Child partition ids
  for (partition_idst::iterator it = partition.child_ids.begin()++;
          it != partition.child_ids.end(); ++it) {
    fill_partition_ids(*it, part_ids);
  }
}
