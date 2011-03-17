/*******************************************************************\

Module: Symex target equation which tracks different partitions for
different deferred functions. Based on symex_target_equation.cpp.

Author: Ondrej Sery

\*******************************************************************/

#include <i2string.h>
#include <std_expr.h>

#include "partitioning_target_equation.h"
#include "expr_pretty_print.h"

/*******************************************************************\

 Function: partitioning_target_equationt::convert

 Inputs:

 Outputs:

 Purpose: Convert all the SSA steps into the corresponding formulas in
 the corresoponding partitions

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
  // Tell the interpolator about the new partition.
  partition.fle_part_id = interpolator.new_partition();

  // Convert the assumption propagation symbols
  partition.callstart_literal = prop_conv.convert(partition.callstart_symbol);
  partition.callend_literal = prop_conv.convert(partition.callend_symbol);

  // If this is a summary partition, apply the summary
  if (partition.is_summary) {
    convert_partition_summary(prop_conv, partition);
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

  for (interpolantst::const_iterator it = partition.summaries->begin();
          it != partition.summaries->end();
          ++it) {
    std::cout << "Substituting interpolant" << std::endl;
    it->substitute(prop_conv, common_symbs);
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
      it != partition.end_it; it++)
  {
    if(it->is_assignment() && !it->ignore)
    {
      exprt tmp(it->cond_expr);

      expr_pretty_print(std::cout << "ASSIGN-OUT:" << std::endl, tmp, 2);

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
      it != partition.end_it; it++)
  {
    if(it->ignore)
      it->guard_literal=const_literal(false);
    else
    {
      exprt tmp(it->guard_expr);

      expr_pretty_print(std::cout << "GUARD-OUT:" << std::endl, tmp, 2);

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
      it != partition.end_it; it++)
  {
    if(it->is_assume())
    {
      if(it->ignore)
        it->cond_literal=const_literal(true);
      else
      {
        exprt tmp(it->cond_expr);

        expr_pretty_print(std::cout << "ASSUME-OUT:" << std::endl, tmp, 2);

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
        it != partition.end_it; it++)
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
      it != partition.end_it; it++) {
    if (it->is_assert())
    {

      expr_pretty_print(std::cout << "ASSERT-OUT:" << std::endl, it->cond_expr, 2);

      // do the expression
      literalt tmp_literal=prop_conv.convert(it->cond_expr);

      it->cond_literal=prop_conv.prop.limplies(assumption_literal, tmp_literal);

      bv.push_back(prop_conv.prop.lnot(it->cond_literal));
    }
    else if (it->is_assume()) {
      // If it is a call end symbol, we need to emit the assumption propagation
      // formula for the given callsite.
      if (number_of_assumptions > 0 && it->cond_expr.id() == ID_symbol) {
        partition_mapt::iterator pit =
                partition_map.find(it->cond_expr.get(ID_identifier));

        if (pit != partition_map.end()) {
          partitiont& target_partition = partitions[pit->second];
          // Emit the assumption propagation formula
          literalt tmp = prop_conv.prop.limplies(target_partition.callstart_literal,
                  assumption_literal);

          prop_conv.prop.l_set_to_true(tmp);

#         if 1
          expr_pretty_print(std::cout << "XXX Call START implication: ",
                  target_partition.callstart_symbol);
          for (SSA_stepst::iterator it2 = partition.start_it; it2 != it; ++it2) {
            if (it2->is_assume()) {
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

  if (partition.parent_id != NO_PARTITION && number_of_assumptions > 0) {
    // Assert the assumption propagation formula for the partition
    literalt tmp = prop_conv.prop.limplies(partition.callend_literal,
            assumption_literal);

#   if 1
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
      it != partition.end_it; it++)
    if(!it->ignore)
    {
      for(std::list<exprt>::const_iterator
          o_it=it->io_args.begin();
          o_it!=it->io_args.end();
          o_it++)
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

 Purpose: Collects information about the specified partions for later
 processing and conversion

\*******************************************************************/

void partitioning_target_equationt::prepare_partitions()
{
  // Fill in the partition start and end iterator for easier access during
  // the conversion process
  int idx = 0;
  SSA_stepst::iterator ssa_it = SSA_steps.begin();

  // The last partition has an undefined end, fix it!
  if (!partitions.empty()) {
    partitions.rbegin()->end_idx = SSA_steps.size();
  }

  for (partitionst::iterator it = partitions.begin();
          it != partitions.end(); ++it) {

    assert(it->filled);

    it->start_it = ssa_it;

    std::cout << idx << ", " << it->start_idx << ", " << it->end_idx << std::endl;
    std::cout << partitions.size() << std::endl;

    while (idx != it->end_idx) {
      assert(ssa_it != SSA_steps.end());
      ++ssa_it;
      ++idx;
    }
    it->end_it = ssa_it;
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
  interpolant_mapt& interpolant_map)
{
  // Prepare the interpolation task. NOTE: ignore the root partition!
  const unsigned valid_partitons = partitions.size()-1;
  interpolation_taskt itp_task(valid_partitons);

  for (unsigned i = 0; i < valid_partitons; ++i) {
    fill_partition_ids(i+1, itp_task[i]);
  }

  // Interpolate...
  interpolantst itp_result;
  itp_result.reserve(valid_partitons);
  interpolator.get_interpolant(itp_task, itp_result);

  // Interpret the result
  std::vector<symbol_exprt> common_symbs;
  interpolant_map.reserve(valid_partitons);
  for (unsigned i = 0; i < valid_partitons; ++i) {
    // Store the intepolant
    partitiont& partition = partitions[i+1];
    interpolant_map.push_back(interpolant_mapt::value_type(
      partition.function_id, interpolantst::value_type()));
    interpolantst::reference interpolant = interpolant_map.back().second;
    interpolant.swap(itp_result[i]);

    // Generalize the interpolant
    fill_common_symbols(partition, common_symbs);

    std::cout << "Common symbols (" << common_symbs.size() << "):" << std::endl;
    for (std::vector<symbol_exprt>::iterator it = common_symbs.begin();
            it != common_symbs.end(); ++it)
      std::cout << it->get_identifier() << std::endl;

    std::cout << "Generalizing interpolant" << std::endl;
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
