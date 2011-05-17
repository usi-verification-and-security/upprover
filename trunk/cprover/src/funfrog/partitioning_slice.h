/*******************************************************************\

Module: Symex slicer modified for partitioning_target _equation. This
module is based on symex_slice_class.h and slice.[cpp/h]

Author: Ondrej Sery

\*******************************************************************/

#ifndef CPROVER_PARTITIONING_SLICE_H
#define CPROVER_PARTITIONING_SLICE_H

#include <goto-symex/slice.h>
#include "partitioning_target_equation.h"

class partitioning_slicet
{
public:
  void slice(partitioning_target_equationt &equation);

protected:
  typedef hash_map_cont<irep_idt, symex_target_equationt::SSA_stept*,
    irep_id_hash> def_mapt;
  typedef hash_map_cont<irep_idt, std::pair<partitioning_target_equationt::partitiont*, unsigned>,
    irep_id_hash> partition_mapt;
  typedef std::multimap<irep_idt, symex_target_equationt::SSA_stept*> assume_mapt;

  symbol_sett processed;
  symbol_sett depends;
  def_mapt def_map;
  partition_mapt summary_map;
  assume_mapt assume_map;

  void prepare_maps(partitioning_target_equationt &equation);
  void prepare_assignment(symex_target_equationt::SSA_stept &SSA_step);
  void prepare_assertion(symex_target_equationt::SSA_stept &SSA_step);
  void prepare_assumption(partitioning_target_equationt &equation,
          symex_target_equationt::SSA_stept &SSA_step);
  void prepare_partition(partitioning_target_equationt::partitiont &partition);
  
  void get_symbols(const typet &type, symbol_sett& symbols);
  void get_symbols(const exprt &expr, symbol_sett& symbols);
};

// Slice an equation with respect to the assertions contained therein
void partitioning_slice(partitioning_target_equationt &equation);

#endif
