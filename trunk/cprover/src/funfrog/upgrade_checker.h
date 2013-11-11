/*******************************************************************

 Module: Upgrade checker using function summaries

 Author: Ondrej Sery

\*******************************************************************/

#ifndef CPROVER_UPGRADE_CHECKER_H
#define	CPROVER_UPGRADE_CHECKER_H

#include "summarizing_checker.h"
#include <ui_message.h>

//#define DEBUG_UPGR

class upgrade_checkert : public summarizing_checkert
{
public:
  upgrade_checkert(
    const goto_programt &_goto_program,
    const goto_functionst &_goto_functions,
    const namespacet &_ns,
    contextt &_context,
    const optionst& _options,
    //std::ostream &_out,
    ui_message_handlert &_message_handler,
    unsigned long &_max_memory_used
    ) : summarizing_checkert (_goto_program, _goto_functions,
    _ns, _context, _options, _message_handler,
    _max_memory_used)
  {};
  
  void initialize();
  bool check_upgrade();
  bool check_summary(const assertion_infot& assertion, 
          summary_infot& summary_info);
  void save_change_impact(){
    omega.serialize_xml(options.get_option("save-change-impact"));
  }

protected:

  void upward_traverse_call_tree(summary_infot& summary_info, bool &pre);
  void downward_traverse_call_tree(summary_infot& summary_info);
  void extract_interpolants (prop_assertion_sumt& prop, partitioning_target_equationt& equation);
  summary_ids_sett checked_summaries;
};

bool check_initial(const namespacet &ns,
  goto_programt &program,
  const goto_functionst &goto_functions,
  const optionst& options,
  ui_message_handlert &_message_handler,
  bool show_progress = true);

bool check_upgrade(const namespacet &ns,
  goto_programt &program_old,
  goto_functionst &goto_functions_old,
  goto_programt &program_new,
  goto_functionst &goto_functions_new,
  const optionst& options,
  ui_message_handlert &_message_handler,
  bool show_progress = true);

#endif
