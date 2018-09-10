/*******************************************************************\

Module: Symex slicer modified for partitioning_target _equation. This
module is based on symex_slice_class.h and slice.[cpp/h]

\*******************************************************************/

#include <util/std_expr.h>

#include "partitioning_slice.h"
#include "partition_iface.h"
#include "solvers/prop_itp.h"
#include "solvers/smt_itp.h"
#include "summary_store.h"
#include "partitioning_target_equation.h"

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

void partitioning_slicet::slice(partitioning_target_equationt & equation, const summary_storet & summary_store)
{
  // Mark assignments as ignored
  for(symex_target_equationt::SSA_stepst::iterator it = 
          equation.SSA_steps.begin();
          it!=equation.SSA_steps.end();
          ++it) {
    // We can only slice assignments
    it->ignore = it->is_assignment();
  }
  for (auto & partition : equation.get_partitions())
  {
    if (partition.has_summary_representation()) {
      partition.applicable_summaries.clear();
      // We can only slice standard summaries, not inverted and not summaries
      // with assertion in subtree
      if (partition.get_iface().assertion_in_subtree) {
        mark_summary_symbols(summary_store, partition);
        partition.ignore = false;
      } else {
        partition.ignore = true;
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
      assert(partition.has_summary_representation());
      const summary_idst& itps = partition.summaries;
      //unsigned symbol_idx = sum_it->second.second;

      // Any of the summaries can match, we need to go through all of them
      // (this may be optimized by precomputation)
      for (unsigned long summary_id : itps) {
          // Already used summary
        if (partition.applicable_summaries.find(summary_id) != 
                partition.applicable_summaries.end())
          continue;
        
        summaryt& summary = summary_store.find_summary(summary_id);
        // Does not restrict the given symbol
        //if (!summary.get_symbol_mask()[symbol_idx]) // TODO: seems broken
        //  continue;
        
        // Yes it is relevant, add only symbols constrained by the summary
        partition.applicable_summaries.insert(summary_id);
        for (unsigned idx = 0; idx < partition_iface.argument_symbols.size(); ++idx) {
            if(summary.usesVar(idx))
            {
                get_symbols(partition_iface.argument_symbols[idx], depends);
            }
        }
      }
      partition.ignore = false;
    }
  }
  
  // Mark sliced out partitions
  for(auto & partition : equation.get_partitions()) {
    // Only care about real partitions
    if (partition.has_abstract_representation()|| partition.ignore ||
            partition.get_iface().assertion_in_subtree)
      continue;
    
    bool ignore = true;
    for(auto it = partition.start_it;
          it != partition.end_it; ++it) {
      if (!it->ignore) {
        ignore = false;
        break;
      }
    }
    if (ignore) {
      //std::cout << "Ignoring partition: " << partition.parent_id << std::endl;
      partition.ignore = ignore;
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
    prepare_partition(*it);
    
    if (it->has_abstract_representation())
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
  //const irep_idt &id2 = SSA_step.ssa_rhs.get(ID_identifier);
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
  if (partition.has_summary_representation()) {
    if (!partition_iface.assertion_in_subtree) {
      if (partition_iface.returns_value) {
        summary_map.insert(summary_mapt::value_type(
                partition_iface.retval_symbol.get_identifier(),
                summary_mapt::value_type::second_type(&partition,
                partition_iface.argument_symbols.size() +
                partition_iface.out_arg_symbols.size() +
                // Yes, this cannot happen in this branch, but just in case...
                (partition_iface.assertion_in_subtree ? 3 : 2))));
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
void partitioning_slicet::mark_summary_symbols(const summary_storet & summary_store,
        partitiont &partition) {
  // Mark all used symbols as directly as dependent
  const partition_ifacet& partition_iface = partition.get_iface();
  const summary_idst& itps = partition.summaries;
  auto iface_symbols = partition_iface.get_iface_symbols();
  // Mark all the used symbols in all summaries
  for (auto summary_id : itps) {
    auto& summary = summary_store.find_summary(summary_id);

    // Add only symbols constrained by the summary
    partition.applicable_summaries.insert(summary_id);

      for (unsigned idx = 0; idx < iface_symbols.size(); ++idx)
      {
          if(summary.usesVar(idx))
              get_symbols(iface_symbols[idx], depends);
      }
  }
}

/*******************************************************************\

Function: partitioning_slice

  Inputs:

 Outputs:

 Purpose: Slice an equation with respect to the assertions contained therein

\*******************************************************************/

void partitioning_slice(partitioning_target_equationt & equation)
{
  partitioning_slicet slice;
    slice.slice(equation, equation.get_summary_store());
}
