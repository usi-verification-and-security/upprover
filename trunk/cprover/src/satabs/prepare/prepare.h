/*******************************************************************\

Module: "Preprocess" C program for CEGAR

Author: Daniel Kroening
        Karen Yorav 

Date: June 2003

Purpose: Preprocess the C program and convert it into a GOTO
         program.

\*******************************************************************/

#ifndef CPROVER_CEGAR_PREPARE_H
#define CPROVER_CEGAR_PREPARE_H

#include <ui_message.h>
#include <options.h>

#include <langapi/language_ui.h>

#include <goto-programs/goto_functions.h>

class preparet:public language_uit
{
public:
  preparet(
    const cmdlinet &_cmdline,
    const optionst &options,
    contextt &_shadow_context);

  bool doit();

  namespacet ns;
  contextt &shadow_context;
  goto_functionst goto_functions;
  std::vector<exprt> user_provided_predicates;
  
  unsigned max_iterations()
  {
    if(cmdline.isset("iterations"))
      return atoi(cmdline.getval("iterations"));

    return 50; // default iterations
  }
  
private:
  const cmdlinet &cmdline;
  const optionst &options;

  void get_predicates();
  void get_initial_state();
  bool get_sync_modules();
  bool get_async_modules();
  
  void replace_dynamic_allocation(goto_programt &goto_program);
  void replace_dynamic_allocation(goto_functionst &goto_functions);
  
  void register_languages();
};

#endif
