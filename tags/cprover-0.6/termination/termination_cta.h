/*******************************************************************\

Module: Termination module: Compositional Termination Analysis

Author: CM Wintersteiger

\*******************************************************************/

#ifndef _CPROVER_TERMINATION_RFF_H_
#define _CPROVER_TERMINATION_RFF_H_

#include <goto-symex/symex_target_equation.h>

#include "termination_path_enumeration.h"
#include "ranking_relation_cache.h"

class concrete_modelt;
class value_setst;

class termination_ctat : public termination_path_enumerationt
{
public:
  termination_ctat(const cmdlinet &_cmd,
                   const goto_functionst &_gf,
                   const contextt &_ctxt,
                   class contextt &_sctxt,
                   class value_set_analysist &_vsa,
                   class invariant_propagationt &_ip,
                   message_handlert &_mh,
                   ui_message_handlert::uit _ui) :
                     termination_path_enumerationt(_cmd, _gf, _ctxt, _sctxt,
                                                   _vsa, _ip, _mh, _ui),
                     ranking_generalization_time(0) {}

  virtual termination_resultt operator()();

  fine_timet ranking_generalization_time;

  virtual void show_stats(void);

protected:
  goto_functionst temp_goto_functions;
  
  termination_resultt
      terminates(
        const irep_idt &main,
        const goto_functionst &goto_functions,
        goto_programt::const_targett assertion);

  termination_resultt rank(
    goto_programt::const_targett &loop_begin,
    goto_programt::targett &loop_end,
    goto_programt::const_targett &copy_goto,    
    replace_idt &premap,
    ranking_relation_cachet &ranking_relations);

  termination_resultt rank_blockwise(
    goto_programt::const_targett &loop_begin,
    goto_programt::const_targett &loop_end,
    goto_programt::const_targett &copy_goto,
    goto_programt::targett &sliced_assertion,
    concrete_modelt &sliced_model,
    replace_idt &premap,
    ranking_relation_cachet &ranking_relations);

  bool rank_block(
    concrete_modelt &model,
    goto_programt::targett &original_assertion,
    goto_programt::targett &original_backjump,
    goto_programt::targett &assertion,
    replace_idt &premap,
    ranking_relation_cachet &ranking_relations,
    const irep_idt &main_backup_id);

  exprt rank_trace(goto_tracet &goto_trace, replace_idt &premap);

  void unwinding_init(    
    const irep_idt &main_backup_id,
    goto_programt::const_targett &loop_begin,
    goto_programt::targett &loop_end,
    goto_programt::const_targett &copy_goto,
    goto_programt::targett &assertion);

  void unwinding_next(    
    goto_programt::const_targett &loop_begin,
    goto_programt::targett &loop_end,
    goto_programt::targett &new_assertion,
    unsigned total_unwindings);

  void unwinding_cleanup(const irep_idt main_backup_id);

  void rename_main(const irep_idt &main_backup_id);
  void unrename_main(const irep_idt &main_backup_id);

  bool all_paths_are_ranked(
    concrete_modelt &temp_model,
    goto_tracet &goto_trace);

  void get_loop_program(
    goto_programt::const_targett &loop_begin,
    goto_programt::targett &loop_end,
    goto_programt::const_targett &copy_goto,
    const goto_functionst &goto_functions,
    goto_programt &dest,
    goto_programt::targett &assertion,
    goto_programt::targett &copy_state,
    goto_programt::targett &backjump);

  exprt weakest_precondition(goto_tracet &goto_trace);

  bool exclude_precondition(
    concrete_modelt &model,
    goto_programt::targett &assertion,
    goto_programt::targett &backjump,
    const irep_idt &main_backup_id,
    goto_tracet &goto_trace);

  bool is_compositional(
    ranking_relation_cachet &ranking_relations,
    replace_idt &premap);
  
  // entry point for methods that try to `rescue' the ranking argument
  virtual bool make_compositional(
    goto_programt::const_targett &loop_begin,
    goto_programt::targett &loop_end,
    goto_programt::const_targett &loop_copy_goto,
    goto_programt::targett &loop_assertion,
    concrete_modelt &model,
    replace_idt &premap,
    ranking_relation_cachet &ranking_relations) { return false; }
};

#endif
