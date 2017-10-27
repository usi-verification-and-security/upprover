/*******************************************************************\

Module: Symex target equation which tracks different partitions for
different deferred functions.

Author: Ondrej Sery

\*******************************************************************/

#ifndef CPROVER_PROP_PARTITIONING_TARGET_EQUATION_H
#define CPROVER_PROP_PARTITIONING_TARGET_EQUATION_H

#include "partitioning_target_equation.h"
#include "solvers/satcheck_opensmt2.h"
#include "partition_iface.h"


// Two classes for smt and prop   
class partitioning_target_equationt;
class prop_partitioning_target_equationt:public partitioning_target_equationt 
{
public:
  prop_partitioning_target_equationt(const namespacet &_ns, summarization_contextt&
          _summarization_context, bool _upgrade_checking,
          bool _store_summaries_with_assertion, coloring_modet _coloring_mode,
          std::vector<unsigned>& _clauses)
            : partitioning_target_equationt(_ns, 
                       _summarization_context, _upgrade_checking,
                       _store_summaries_with_assertion, _coloring_mode,
                       _clauses) {}
            
  // Convert all the SSA steps into the corresponding formulas in
  // the corresponding partitions
  void convert(prop_conv_solvert &prop_conv, interpolating_solvert &interpolator);
  
  // Extract interpolants corresponding to the created partitions
  void extract_interpolants(
    interpolating_solvert& interpolator, const prop_conv_solvert& decider,
    interpolant_mapt& interpolant_map);

protected:
  // Convert a specific partition of SSA steps
  void convert_partition(prop_conv_solvert &prop_conv_solvert,
    interpolating_solvert &interpolator, partitiont& partition);
  // Convert a specific partition guards of SSA steps
  void convert_partition_guards(prop_conv_solvert &prop_conv,
    partitiont& partition);
  // Convert a specific partition assignments of SSA steps
  void convert_partition_assignments(prop_conv_solvert &prop_conv,
    partitiont& partition);
  // Convert a specific partition assumptions of SSA steps
  void convert_partition_assumptions(prop_conv_solvert &prop_conv,
    partitiont& partition);
  // Convert a specific partition assertions of SSA steps
  void convert_partition_assertions(prop_conv_solvert &prop_conv,
    partitiont& partition);
  // Convert a specific partition io of SSA steps
  void convert_partition_io(prop_conv_solvert &prop_conv,
    partitiont& partition);
  // Convert a summary partition (i.e., assert its summary)
  void convert_partition_summary(prop_conv_solvert &prop_conv,
    partitiont& partition);
  // Convert a specific partition gotos of SSA steps
  void convert_partition_goto_instructions(prop_conv_solvert &prop_conv,
    partitiont& partition);
  
  // Override
  virtual void fill_partition_ids(partition_idt partition_id, fle_part_idst& part_ids);
  
  virtual bool is_smt_encoding() {return false;} // KE: Temp. Just to force virtual for compilation
};

#endif