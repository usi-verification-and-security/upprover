/*******************************************************************\

Module: Symex slicer modified for partitioning_target _equation. This
module is based on symex_slice_class.h and slice.[cpp/h]

Author: Ondrej Sery

\*******************************************************************/

#include <hash_cont.h>
#include <std_expr.h>

#include "partitioning_slice.h"

/*******************************************************************\

Function: partitioning_slicet::get_symbols

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void partitioning_slicet::get_symbols(const exprt &expr, symbol_sett& symbols)
{
  get_symbols(expr.type(), symbols);

  forall_operands(it, expr)
    get_symbols(*it, symbols);

  if(expr.id()==ID_symbol) {
    const irep_idt& id = to_symbol_expr(expr).get_identifier();
    if (processed.find(id) == processed.end()) {
      symbols.insert(id);
    }
  }
}

/*******************************************************************\

Function: partitioning_slicet::get_symbols

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void partitioning_slicet::get_symbols(const typet &type, symbol_sett& symbols)
{
  // TODO
}

/*******************************************************************\

Function: partitioning_slicet::slice

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void partitioning_slicet::slice(partitioning_target_equationt &equation)
{
  // Mark assignments and assumptions as ignored
  for(symex_target_equationt::SSA_stepst::iterator it = 
          equation.SSA_steps.begin();
          it!=equation.SSA_steps.end();
          ++it) {
    if (it->is_assignment() || it->is_assume())
      it->ignore = true;
  }
  for (partitioning_target_equationt::partitionst::iterator it = 
          equation.partitions.begin();
          it != equation.partitions.end();
          ++it)
  {
    if (it->is_summary)
      it->ignore = true;
  }

  // Prepare necessary maps
  prepare_maps(equation);

  // Propagate the values
  while (!depends.empty()) {
    // Remove one
    irep_idt id = *depends.begin();
    depends.erase(depends.begin());
    
    // Mark as processed
    processed.insert(id);

    // Is it assigned?
    def_mapt::iterator def_it = def_map.find(id);
    if (def_it != def_map.end()) {
      get_symbols(def_it->second->guard_expr, depends);
      get_symbols(def_it->second->rhs, depends);
      def_it->second->ignore = false;
    }
      
    // Is constrained by assumptions?
    std::pair<assume_mapt::iterator, assume_mapt::iterator> ass_rng =
            assume_map.equal_range(id);
    if (ass_rng.first != ass_rng.second) {
      // FIXME: Too strict...the assumption might not be on path to any 
      // assertion
      for (assume_mapt::iterator it = ass_rng.first;
              it != ass_rng.second;
              ++it) {
        get_symbols(it->second->guard_expr, depends);
        get_symbols(it->second->cond_expr, depends);
        it->second->ignore = false;
      }
    }
    
    // Is constrained by a summary?
    partition_mapt::iterator sum_it = summary_map.find(id);
    if (sum_it != summary_map.end()) {
      partitioning_target_equationt::partitiont& partition =
              *(sum_it->second.first);
      const interpolantst& itps = *partition.summaries;
      unsigned symbol_idx = sum_it->second.second;

      // Any of the summaries can match, we need to go through all of them
      // (this may be optimized by precomputation)
      for (unsigned i = 0; i < itps.size(); ++i) {
        // Already used summary
        if (partition.applicable_summaries.find(i) != partition.applicable_summaries.end())
          continue;
        
        // Does not restrict the given symbol
        if (!itps[i].get_symbol_mask()[symbol_idx])
          continue;
        
        // Yes it is relevant, add only symbols constrained by the summary
        unsigned idx = 0;
        partition.applicable_summaries.insert(i);
        for (std::vector<symbol_exprt>::iterator it = 
                partition.argument_symbols.begin();
                it != partition.argument_symbols.end();
                ++it, ++idx) {
          if (itps[i].get_symbol_mask()[idx])
            get_symbols(*it, depends);
        }
      }
      partition.ignore = false;
    }
  }
}

/*******************************************************************\

Function: partitioning_slicet::prepare_maps

  Inputs:

 Outputs:

 Purpose: Precomputes def_map, summary_map, and assume_map for later 
 use during slicing. More over, depends map is initialized to all symbols 
 used in assertions.

\*******************************************************************/
void partitioning_slicet::prepare_maps(partitioning_target_equationt &equation) 
{
  // Analyze the SSA steps
  for (symex_target_equationt::SSA_stepst::iterator it = 
          equation.SSA_steps.begin();
          it != equation.SSA_steps.end();
          ++it) 
  {
    if (it->is_assignment())
    {  
      prepare_assignment(*it);
    } 
    else if (it->is_assume())
    {
      prepare_assumption(equation, *it);
    } 
    else if (it->is_assert())
    {
      prepare_assertion(*it);
    }
  }
  
  // Analyze the partitions
  for (partitioning_target_equationt::partitionst::iterator it = 
          equation.partitions.begin();
          it != equation.partitions.end();
          ++it)
  {
    prepare_partition(*it);
  }
}

/*******************************************************************\

Function: partitioning_slicet::prepare_assertion

  Inputs:

 Outputs:

 Purpose: Symbols in cond. & guard are marked in the depends set.

\*******************************************************************/

void partitioning_slicet::prepare_assertion(
        symex_target_equationt::SSA_stept &SSA_step) 
{
  get_symbols(SSA_step.guard_expr, depends);
  get_symbols(SSA_step.cond_expr, depends);
}

/*******************************************************************\

Function: partitioning_slicet::prepare_assignment

  Inputs:

 Outputs:

 Purpose: Mark lhs in the def_map

\*******************************************************************/

void partitioning_slicet::prepare_assignment(
        symex_target_equationt::SSA_stept &SSA_step) 
{
  assert(SSA_step.lhs.id() == ID_symbol);

  const irep_idt &id = SSA_step.lhs.get(ID_identifier);
  def_map.insert(def_mapt::value_type(id, &SSA_step));
}

/*******************************************************************\

Function: partitioning_slicet::prepare_assumption

  Inputs:

 Outputs:

 Purpose: All referred symbols go to assume_map. Call_end assumption
 are mapped to out args. and return value.

\*******************************************************************/

void partitioning_slicet::prepare_assumption(
        partitioning_target_equationt &equation,
        symex_target_equationt::SSA_stept &SSA_step) 
{
  // Collect referred symbols
  symbol_sett s;
  get_symbols(SSA_step.cond_expr, s);
  for (symbol_sett::iterator it = s.begin(); it != s.end(); ++it) {
    assume_map.insert(assume_mapt::value_type(*it, &SSA_step));
  }
  s.clear();

  // If it is a call_end assumption --> add dependency on out args + ret_val
  if (SSA_step.cond_expr.id() == ID_symbol) {
    const irep_idt& sid = to_symbol_expr(SSA_step.cond_expr).get_identifier();
    partitioning_target_equationt::partition_mapt::iterator p_it =
            equation.partition_map.find(sid);

    if (p_it != equation.partition_map.end()) {
      partitioning_target_equationt::partitiont& partition =
              equation.partitions[p_it->second];

      for (std::vector<symbol_exprt>::iterator it =
              partition.out_arg_symbols.begin();
              it != partition.out_arg_symbols.end();
              ++it) {
        assume_map.insert(assume_mapt::value_type(it->get_identifier(), &SSA_step));
      }
      if (partition.returns_value) {
        assume_map.insert(assume_mapt::value_type(
                partition.retval_symbol.get_identifier(), &SSA_step));
      }
    }
  }
}
/*******************************************************************\

Function: partitioning_slicet::prepare_partition

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void partitioning_slicet::prepare_partition(
        partitioning_target_equationt::partitiont &partition) 
{
  // Fill summary table
  if (partition.is_summary) {
    if (partition.returns_value) {
      summary_map.insert(partition_mapt::value_type(
              partition.retval_symbol.get_identifier(), 
              partition_mapt::value_type::second_type(&partition,
              partition.argument_symbols.size() + 
              partition.out_arg_symbols.size() + 2)));
    }
    unsigned symbol_idx = partition.argument_symbols.size();
    for (std::vector<symbol_exprt>::iterator it2 =
            partition.out_arg_symbols.begin();
            it2 != partition.out_arg_symbols.end();
            ++it2, ++symbol_idx) {
      summary_map.insert(partition_mapt::value_type(
              it2->get_identifier(), 
              partition_mapt::value_type::second_type(&partition, symbol_idx)));
    }
  }
  // All call start symbols to dependencies (we need all their assumptions 
  // for constraint call symbols constraints propagation)
  get_symbols(partition.callstart_symbol, depends);
}

/*******************************************************************\

Function: partitioning_slice

  Inputs:

 Outputs:

 Purpose: Slice an equation with respect to the assertions contained therein

\*******************************************************************/

void partitioning_slice(partitioning_target_equationt &equation)
{
  partitioning_slicet slice;
  slice.slice(equation);
}
