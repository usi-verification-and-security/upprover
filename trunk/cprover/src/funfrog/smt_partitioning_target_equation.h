/*******************************************************************\

Module: Symex target equation which tracks different partitions for
different deferred functions.

Author: Ondrej Sery

\*******************************************************************/

#ifndef CPROVER_SMT_PARTITIONING_TARGET_EQUATION_H
#define CPROVER_SMT_PARTITIONING_TARGET_EQUATION_H

#include "partitioning_target_equation.h"
#include "partition_iface_fwd.h"

class smtcheck_opensmt2t;
class interpolating_solvert;

// Two classes for smt and prop   
class smt_partitioning_target_equationt:public partitioning_target_equationt
{
public:
  smt_partitioning_target_equationt(const namespacet &_ns, summarization_contextt&
          _summarization_context, bool _upgrade_checking,
          bool _store_summaries_with_assertion, coloring_modet _coloring_mode,
          std::vector<unsigned>& _clauses)
            : partitioning_target_equationt(_ns, 
                       _summarization_context, _upgrade_checking,
                       _store_summaries_with_assertion, _coloring_mode,
                       _clauses) {}
            
  // Convert all the SSA steps into the corresponding formulas in
  // the corresponding partitions
  void convert(smtcheck_opensmt2t &decider, interpolating_solvert &interpolator);
  
  void fill_function_templates(smtcheck_opensmt2t &decider, std::vector<summaryt*> &templates);
  
  // Extract interpolants corresponding to the created partitions
  void extract_interpolants(smtcheck_opensmt2t& decider, interpolant_mapt& interpolant_map);

  std::vector<exprt>& get_exprs_to_refine () { return exprs; };

  void fill_common_symbols(const partitiont &partition,
                           std::vector<symbol_exprt> &common_symbols) const override;

protected:

  std::vector<exprt> exprs;

  // Convert a specific partition of SSA steps
  void convert_partition(smtcheck_opensmt2t &decider,
    interpolating_solvert &interpolator, partitiont& partition);
  // Convert a specific partition guards of SSA steps
  void convert_partition_guards(smtcheck_opensmt2t &decider,
    partitiont& partition);
  // Convert a specific partition assignments of SSA steps
  void convert_partition_assignments(smtcheck_opensmt2t &decider,
    partitiont& partition);
  // Convert a specific partition assumptions of SSA steps
  void convert_partition_assumptions(smtcheck_opensmt2t &decider,
    partitiont& partition);
  // Convert a specific partition assertions of SSA steps
  void convert_partition_assertions(smtcheck_opensmt2t &decider,
    partitiont& partition);
  // Convert a specific partition io of SSA steps
  void convert_partition_io(smtcheck_opensmt2t &decider,
    partitiont& partition);
  // Convert a summary partition (i.e., assert its summary)
  void convert_partition_summary(smtcheck_opensmt2t &decider,
    partitiont& partition);
  // Convert a specific partition gotos of SSA steps
  void convert_partition_goto_instructions(smtcheck_opensmt2t &decider,
    partitiont& partition);
  
private:
  bool isRoundModelEq(const exprt &expr); // Detect the case of added round var for rounding model- not needed in LRA!
  
  
  bool isTypeCastConst(const exprt &expr); // Only for debugging typecast
};
#endif
