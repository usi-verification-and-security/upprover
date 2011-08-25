/*******************************************************************\

Module: Termination module: the path enumeration method

Author: CM Wintersteiger

\*******************************************************************/

#ifndef _CPROVER_TERMINATION_PATH_ENUMERATION_H_
#define _CPROVER_TERMINATION_PATH_ENUMERATION_H_

#include <goto-symex/symex_target_equation.h>

#include "termination_bre.h"
#include "ranking_relation_cache.h"

class concrete_modelt;
class value_setst;

class termination_path_enumerationt : public termination_bret
{
public:
  termination_path_enumerationt(const cmdlinet &_cmd,
                                const goto_functionst &_gf,
                                const contextt &_ctxt,
                                class contextt &_sctxt,
                                class value_set_analysist &_vsa,
                                class invariant_propagationt &_ip,
                                message_handlert &_mh,
                                ui_message_handlert::uit _ui) :
                                  termination_bret(_cmd, _gf, _ctxt, _sctxt, 
                                                   _vsa, _ip, _mh, _ui),                     
                                  pointer_analysis_time(0),
                                  wp_ce_extraction_time(0),
                                  wp_unreachability_time(0),
                                  path_feasibility_time(0),
                                  ranking_cache_time(0),
                                  loop_reachability_time(0),                                  
                                  paths_analyzed(0),
                                  paths_infeasible(0),
                                  ranking_relations(ns, _mh) 
  {
    ranking_relations.set_verbosity(verbosity);
    ranking_relations.set_message_handler(get_message_handler());
  }
  
  virtual termination_resultt operator()();
  
  std::string ranking_mode;
  
  fine_timet pointer_analysis_time;
  fine_timet wp_ce_extraction_time;
  fine_timet wp_unreachability_time;
  fine_timet path_feasibility_time;
  fine_timet ranking_cache_time;
  fine_timet loop_reachability_time;
  
  unsigned paths_analyzed;
  unsigned paths_infeasible;
  
  virtual void show_stats(void);
  
protected:
  goto_functionst sliced_goto_functions;
  goto_programt::targett sliced_assertion;
  
  termination_resultt
      terminates(
        const irep_idt &main,
        const goto_functionst &goto_functions,
        goto_programt::const_targett assertion);
    
  typedef std::map<goto_programt::const_targett, bool> path_mapt;  
  
  ranking_relation_cachet ranking_relations;
  
  void get_pre_post_mapping(
    goto_programt::const_targett &loop_begin,
    goto_programt::const_targett &loop_end,
    class replace_idt &premap) const;
  
  void get_loop_extent(
    goto_programt::targett &assertion,
    goto_programt::const_targett &begin,
    goto_programt::const_targett &end,
    goto_programt::const_targett &copy_goto);
  
  bool get_model(
    const irep_idt &main,
    const goto_functionst &goto_functions,
    goto_programt::const_targett assertion);
  
  termination_resultt rank(
    goto_programt::const_targett &loop_begin,
    goto_programt::const_targett &loop_end,
    goto_programt::const_targett &copy_goto,
    replace_idt &premap,
    ranking_relation_cachet &ranking_relations);
  
  termination_resultt rank_pathwise(
    goto_programt::const_targett &loop_begin,
    goto_programt::const_targett &loop_end,
    goto_programt::const_targett &copy_goto,
    goto_programt::targett &sliced_assertion,
    concrete_modelt &sliced_model,
    replace_idt &premap,
    ranking_relation_cachet &ranking_relations);
  
  bool precondition_is_reachable(const exprt &precondition);
  
  termination_resultt check_rank_relations(     
    ranking_relation_cachet &ranking_relations);
  
  void get_loop_program(
    goto_programt::const_targett &loop_begin,
    goto_programt::const_targett &loop_end,
    goto_programt::const_targett &copy_goto,
    const goto_functionst &goto_functions,
    goto_programt &dest,
    goto_programt::targett &assertion,
    goto_programt::targett &copy_state,
    goto_programt::targett &backjump);
  
  void initialize_paths(
    goto_programt::const_targett &begin, 
    goto_programt::const_targett &end,
    path_mapt &path_map);
  
  bodyt extract_path(
    goto_programt::const_targett &loop_begin,
    goto_programt::const_targett &loop_end,
    const path_mapt &path_map);
  
  exprt weakest_precondition(
    goto_programt::const_targett &loop_begin,
    goto_programt::const_targett &loop_end,
    goto_programt::const_targett &copy_goto,
    const path_mapt &path_map,
    value_setst &va);
  
  void ssa_replace(
    exprt &expr,
    replace_idt &replace_id,
    std::map<irep_idt, unsigned> &ssa_counters) const;
  
  bool get_next_path(path_mapt &path_map) const;
  std::string path_string(const path_mapt &path_map) const;
  
  bool is_reachable(
    goto_programt::const_targett &loop_begin, 
    goto_programt::const_targett &loop_end,
    bool use_bmc=false);
    
  bool is_local(
    goto_programt::targett loop_begin, 
    goto_programt::targett loop_end);
  bool is_feasible(bodyt &body);
  bool is_terminating_bre(concrete_modelt &model);
};

#endif
