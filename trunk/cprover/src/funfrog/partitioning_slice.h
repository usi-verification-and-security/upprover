/*******************************************************************\

Module: Symex slicer modified for partitioning_target _equation. This
module is based on symex_slice_class.h and slice.[cpp/h]

\*******************************************************************/

#ifndef CPROVER_PARTITIONING_SLICE_H
#define CPROVER_PARTITIONING_SLICE_H

#include <goto-symex/slice.h>

class partitioning_target_equationt;
class SSA_stept;
class summary_storet;
class partitiont;

class partitioning_slicet
{
public:
  void slice(partitioning_target_equationt & equation, const summary_storet & summary_store);

protected:
  typedef std::unordered_map<irep_idt, SSA_stept*,
    irep_id_hash> def_mapt;
  typedef std::unordered_map<irep_idt, std::pair<partitiont*, unsigned>,
    irep_id_hash> summary_mapt;
  typedef std::multimap<irep_idt, SSA_stept*> assume_mapt;

  symbol_sett processed;
  symbol_sett depends;
  def_mapt def_map;
  summary_mapt summary_map;
  assume_mapt assume_map;

  void prepare_maps(partitioning_target_equationt &equation);
  void prepare_assignment(SSA_stept &SSA_step);
  void prepare_assertion(SSA_stept &SSA_step);
  void prepare_assumption(partitioning_target_equationt &equation,
          SSA_stept &SSA_step);
  void prepare_partition(partitiont &partition);
  
  void mark_summary_symbols(const summary_storet & summary_store,
        partitiont &partition);
  
  void get_symbols(const typet &type, symbol_sett& symbols);
  void get_symbols(const exprt &expr, symbol_sett& symbols);
};

// Slice an equation with respect to the assertions contained therein
void partitioning_slice(partitioning_target_equationt & equation);

#endif
