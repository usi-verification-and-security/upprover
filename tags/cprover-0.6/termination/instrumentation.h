/*******************************************************************\

Module: Termination instrumentation

Author: CM Wintersteiger

\*******************************************************************/

#ifndef CPROVER_GOTO_PROGRAMS_TERMINATION_H
#define CPROVER_GOTO_PROGRAMS_TERMINATION_H

#include <set>

#include <namespace.h>
#include <message.h>
#include <context.h>
#include <find_symbols.h>

#include <goto-programs/goto_program.h>
#include <goto-programs/goto_functions.h>

class termination_instrumentert:public messaget
{
public:
  typedef enum { T_DIRECT, T_RANKSYNTH } modet;
  
  termination_instrumentert(goto_functionst &_gf,
                            contextt &_context,
                            message_handlert &_mh,
                            modet _mode=T_RANKSYNTH);
  ~termination_instrumentert();

  unsigned instrument(bool copy_state=true);

protected:
  typedef find_symbols_sett variantt;
  
  struct loopt
  {
    goto_programt::targett begin, end;
    variantt variant;
  };
  
  typedef std::map<irep_idt, irep_idt> var_mapt;
  typedef std::map<irep_idt, variantt > globals_cachet;
  
  goto_functionst &goto_functions;
  contextt &context;
  namespacet ns;
  modet mode;
  
  globals_cachet globals_cache;
  
  unsigned loop_counter;
  unsigned tmp_symbol_cnt;
  
  
  unsigned instrument(goto_programt &program, bool copy_state=true);

  void get_variant(
    loopt &loop,
    bool only_globals=false);
  
  void instrument_loop(
    loopt &loop, 
    goto_programt &program, 
    bool copy_state=true);
  
  bool make_old_variables(
    loopt &loop, 
    goto_programt &program,
    var_mapt &var_map);
  
  
  exprt add_copied_flag(
    loopt &loop,
    goto_programt &program);
  
  exprt generate_termination_assertion(
    const exprt &copied_flag,
    const var_mapt &var_map) const;
  
  void insert_assertion(loopt &loop,
                        const exprt &copied_flag,
                        const var_mapt &var_map,
                        goto_programt &program);
  
  bool is_global(const irep_idt &ident) const;
  
  void add_globals(const exprt &expr, find_symbols_sett &dest) const;
};

#endif
