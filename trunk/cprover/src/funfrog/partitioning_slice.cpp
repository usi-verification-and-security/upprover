/*******************************************************************\

Module: Symex slicer modified for partitioning_target _equation. This
module is based on symex_slice_class.h and slice.[cpp/h]

Author: Ondrej Sery

\*******************************************************************/

#include <std_expr.h>

#include "partitioning_slice.h"

//#define DEBUG_SLICER

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
#     ifdef DEBUG_SLICER
      std::cerr << "Marking: '" << id << "'" << std::endl;
#     endif
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

void partitioning_slicet::slice(partitioning_target_equationt &equation,
        summary_storet& summary_store)
{
  // Mark assignments as ignored
  for(symex_target_equationt::SSA_stepst::iterator it = 
          equation.SSA_steps.begin();
          it!=equation.SSA_steps.end();
          ++it) {
    // We can only slice assignments
    it->ignore = it->is_assignment();
  }
  for (partitionst::iterator it = equation.get_partitions().begin();
          it != equation.get_partitions().end();
          ++it)
  {
    if (it->summary) {
      it->applicable_summaries.clear();
      // We can only slice standard summaries, not inverted and not summaries
      // with assertion in subtree
      if (it->inverted_summary || it->get_iface().assertion_in_subtree) {
        mark_summary_symbols(summary_store, *it);
        it->ignore = false;
      } else {
        it->ignore = true;
      }
    }
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
      get_symbols(def_it->second->guard, depends);
      get_symbols(def_it->second->ssa_rhs, depends);
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
        get_symbols(it->second->guard, depends);
        get_symbols(it->second->cond_expr, depends);
        it->second->ignore = false;


      }
    }
    
    // Is constrained by a summary?
    summary_mapt::iterator sum_it = summary_map.find(id);
    if (sum_it != summary_map.end()) {
      partitiont& partition = *(sum_it->second.first);
      partition_ifacet& partition_iface = partition.get_iface();
      const summary_idst& itps = *partition.summaries;
      //unsigned symbol_idx = sum_it->second.second;

      // Any of the summaries can match, we need to go through all of them
      // (this may be optimized by precomputation)
      for (summary_idst::const_iterator it = itps.begin();
              it != itps.end(); ++it) 
      {
        summary_idt summary_id = *it;
        // Already used summary
        if (partition.applicable_summaries.find(summary_id) != 
                partition.applicable_summaries.end())
          continue;
        
        summaryt& summary = summary_store.find_summary(summary_id);
        // Does not restrict the given symbol
        //if (!summary.get_symbol_mask()[symbol_idx]) // TODO: seems broken
        //  continue;
        
        // Yes it is relevant, add only symbols constrained by the summary
        unsigned idx = 0;
        partition.applicable_summaries.insert(summary_id);
        for (std::vector<symbol_exprt>::iterator it2 = 
                partition_iface.argument_symbols.begin();
                it2 != partition_iface.argument_symbols.end();
                ++it2, ++idx) {
            // SAT checks idx, SMT checks it2
            if(summary.usesVar(*it2,idx))
            {
                get_symbols(*it2, depends);
            }
        }
      }
      partition.ignore = false;
    }
  }
  
  // Mark sliced out partitions
  for(partitionst::iterator it = 
          equation.get_partitions().begin();
          it != equation.get_partitions().end();
          ++it) {
    // Only care about real partitions
    if (it->summary || it->invalid || it->ignore ||
            it->get_iface().assertion_in_subtree)
      continue;
    
    bool ignore = true;
    for(symex_target_equationt::SSA_stepst::iterator it2 = it->start_it;
          it2 != it->end_it; ++it2) {
      if (!it2->ignore) {
        ignore = false;
        break;
      }
    }
    if (ignore) {
      std::cout << "Ignoring partition: " << it->parent_id << std::endl;
      it->ignore = ignore;
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
  // Analyze the partitions
  for (partitionst::iterator it = equation.get_partitions().begin();
          it != equation.get_partitions().end();
          ++it)
  {
    if (it->invalid)
      continue;

    prepare_partition(*it);
    
    if (it->summary || it->stub)
      continue;

    // Analyze the SSA steps
    for (symex_target_equationt::SSA_stepst::iterator it2 = it->start_it;
            it2 != it->end_it;
            ++it2) {
      if (it2->is_assignment()) {
        prepare_assignment(*it2);
      }
      else if (it2->is_assume()) {
        prepare_assumption(equation, *it2);
      }
      else if (it2->is_assert()) {
        prepare_assertion(*it2);
      }
    }
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
  get_symbols(SSA_step.guard, depends);
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
  assert(SSA_step.ssa_lhs.id() == ID_symbol);

  const irep_idt &id = SSA_step.ssa_lhs.get(ID_identifier);
  const irep_idt &id2 = SSA_step.ssa_rhs.get(ID_identifier);
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
  // If it is a call_end assumption --> add dependency on out args + ret_val
  if (SSA_step.cond_expr.id() == ID_symbol) {

    // Collect referred symbols
    symbol_sett s;
    get_symbols(SSA_step.cond_expr, s);
    for (symbol_sett::iterator it = s.begin(); it != s.end(); ++it) {
      assume_map.insert(assume_mapt::value_type(*it, &SSA_step));
    }
    s.clear();

    const irep_idt& sid = to_symbol_expr(SSA_step.cond_expr).get_identifier();
    partition_mapt::iterator p_it = equation.partition_map.find(sid);

    if (p_it != equation.partition_map.end()) {
      partitiont& partition = equation.get_partitions()[p_it->second];
      partition_ifacet &partition_iface = partition.get_iface();

      for (std::vector<symbol_exprt>::iterator it =
              partition_iface.out_arg_symbols.begin();
              it != partition_iface.out_arg_symbols.end();
              ++it) {
        assume_map.insert(assume_mapt::value_type(it->get_identifier(), &SSA_step));
      }
      if (partition_iface.returns_value) {
        assume_map.insert(assume_mapt::value_type(
                partition_iface.retval_symbol.get_identifier(), &SSA_step));
      }
    }
  } else {
      // we treat assumption as assertion in a sense that
      // we must use its variables for the dependency-analysis
      prepare_assertion(SSA_step);
  }
}
/*******************************************************************\

Function: partitioning_slicet::prepare_partition

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void partitioning_slicet::prepare_partition(partitiont &partition) 
{
  partition_ifacet & partition_iface = partition.get_iface();
  // For a standard summary without assertion_in_subtree, fill the summary table
  if (partition.summary) {
    if (!partition.inverted_summary &&
            !partition_iface.assertion_in_subtree) {
      if (partition_iface.returns_value) {
        summary_map.insert(summary_mapt::value_type(
                partition_iface.retval_symbol.get_identifier(),
                summary_mapt::value_type::second_type(&partition,
                partition_iface.argument_symbols.size() +
                partition_iface.out_arg_symbols.size() +
                // Yes, this cannot happen in this branch, but just in case...
                partition_iface.assertion_in_subtree ? 3 : 2)));
      }
      unsigned symbol_idx = partition_iface.argument_symbols.size();
      for (std::vector<symbol_exprt>::iterator it2 =
              partition_iface.out_arg_symbols.begin();
              it2 != partition_iface.out_arg_symbols.end();
              ++it2, ++symbol_idx) {
        summary_map.insert(summary_mapt::value_type(
                it2->get_identifier(),
                summary_mapt::value_type::second_type(&partition, symbol_idx)));
      }
    }
  }
  // All call start symbols to dependencies (we need all their assumptions 
  // for constraint call symbols constraints propagation)
  if (partition_iface.callstart_symbol.get_identifier() != ID_nil) {
    get_symbols(partition_iface.callstart_symbol, depends);
  }
  if (partition_iface.error_symbol.get_identifier() != ID_nil) {
    get_symbols(partition_iface.error_symbol, depends);
  }
}

/*******************************************************************\

Function: partitioning_slicet::mark_summary_symbols

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void partitioning_slicet::mark_summary_symbols(summary_storet& summary_store, 
        partitiont &partition) {
  // Mark all used symbols as directly as dependent
  partition_ifacet& partition_iface = partition.get_iface();
  const summary_idst& itps = *partition.summaries;

  // Mark all the used symbols in all summaries
  for (summary_idst::const_iterator it = itps.begin();
          it != itps.end(); ++it) {
    summary_idt summary_id = *it;
    
    // Skip summaries that were not used in the last verification run
    if (partition.inverted_summary &&
            partition.used_summaries.find(summary_id) ==
            partition.used_summaries.end()) {
      
#     ifdef DEBUG_SLICER      
      std::cerr << "Unused summary in inverted summary: " << summary_id << " (used: ";
      for (summary_ids_sett::const_iterator it2 = partition.used_summaries.begin();
              it2 != partition.used_summaries.end();
              ++it2) {
        std::cerr << *it2;
      }
      std::cerr << ")" << std::endl;
#     endif
      
      continue;
    }

    summaryt& summary = summary_store.find_summary(summary_id);

    // Add only symbols constrained by the summary
    unsigned idx = 0;
    partition.applicable_summaries.insert(summary_id);
    // Input argument symbols
    for (std::vector<symbol_exprt>::iterator it2 =
            partition_iface.argument_symbols.begin();
            it2 != partition_iface.argument_symbols.end();
            ++it2, ++idx) {
      // SAT checks idx, SMT checks it2
      if(summary.usesVar(*it2,idx)) // Only SAT uses it
        get_symbols(*it2, depends);
    }
    // Output argument symbols
    for (std::vector<symbol_exprt>::iterator it2 =
            partition_iface.out_arg_symbols.begin();
            it2 != partition_iface.out_arg_symbols.end();
            ++it2, ++idx) {
      // SAT checks idx, SMT checks it2
      if(summary.usesVar(*it2,idx)) // Only SAT uses it
        get_symbols(*it2, depends);
    }
    // Return value symbol
    if (partition_iface.returns_value) {
      // SAT checks idx, SMT checks it2
      if(summary.usesVar(*it2,idx)) // Only SAT uses it
        get_symbols(partition_iface.retval_symbol, depends);
    }
  }
}

/*******************************************************************\

Function: partitioning_slice

  Inputs:

 Outputs:

 Purpose: Slice an equation with respect to the assertions contained therein

\*******************************************************************/

void partitioning_slice(partitioning_target_equationt &equation,
        summary_storet& summary_store)
{
  partitioning_slicet slice;
  slice.slice(equation, summary_store);
}
