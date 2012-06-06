/*******************************************************************\

Module: Termination module: Interpolating Termination Analysis

Author: CM Wintersteiger

\*******************************************************************/

#ifndef _CPROVER_TERMINATION_ITA_H_
#define _CPROVER_TERMINATION_ITA_H_

#include "termination_cta.h"

class termination_itat : public termination_ctat
{
public:
  termination_itat(const cmdlinet &_cmd,
                   const goto_functionst &_gf,
                   const contextt &_ctxt,
                   class contextt &_sctxt,
                   class value_set_analysist &_vsa,
                   class invariant_propagationt &_ip,
                   message_handlert &_mh,
                   ui_message_handlert::uit _ui) :
                     termination_ctat(_cmd, _gf, _ctxt, _sctxt, 
                                      _vsa, _ip, _mh, _ui) {}

  virtual termination_resultt operator()();

  fine_timet interpolation_time;

  virtual void show_stats(void);

protected:
  
  virtual bool make_compositional(
    goto_programt::const_targett &loop_begin,
    goto_programt::targett &loop_end,
    goto_programt::const_targett &loop_copy_goto,
    goto_programt::targett &loop_assertion,
    concrete_modelt &model,
    replace_idt &premap,
    ranking_relation_cachet &ranking_relations);
  
  void copy(
    goto_programt::const_targett &loop_begin,
    goto_programt::targett &loop_end,
    goto_programt::const_targett &copy_goto, 
    goto_programt &dest) const;
};

#endif
