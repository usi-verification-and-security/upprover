/*******************************************************************\

Module: Command Line Parsing

\*******************************************************************/

#ifndef CPROVER_FUNFROG_PARSEOPTIONS_H
#define CPROVER_FUNFROG_PARSEOPTIONS_H

#include <fstream>
#include <cstdlib>
#include <langapi/language_util.h>

#include <util/options.h>
#include "xml_interface.h"

#include <goto-programs/goto_trace.h>

#include <util/ui_message.h>
#include <util/parse_options.h>

#include <goto-programs/goto_functions.h>
#include <pointer-analysis/value_sets.h>

#include <goto-programs/goto_model.h>

class value_set_alloc_adaptort;

#define FUNFROG_OPTIONS \
  "D:I:(16)(32)(64)(v):(version)" \
  "(i386-linux)(i386-macos)(ppc-macos)" \
  "(show-program)(show-fpfreed-program)(show-dereferenced-program)" \
  "(save-program)(save-fpfreed-program)(save-dereferenced-program)" \
  "(show-transformed-program)(show-inlined-program)" \
  "(save-transformed-program)(save-inlined-program)" \
  "(show-claimed-program)(show-abstracted-program)" \
  "(save-claimed-program)(save-abstracted-program)" \
  "(save-summaries):(load-summaries):" \
  "(save-omega):(load-omega):" \
  "(show-symbol-table)(show-value-sets)" \
  "(save-claims)" \
  "(xml-ui)(xml-interface)" \
  "(no-slicing)(no-assert-grouping)(no-summary-optimization)" \
  "(pointer-check)(bounds-check)(div-by-zero-check)(overflow-check)(nan-check)" \
  "(string-abstraction)(assertions)" \
  "(show-pass)(suppress-fail)(no-progress)" \
  "(show-claims)(claims-count)(all-claims)(claims-opt):(claim):(claimset):" \
  "(theoref)(force)(custom):(heuristic):(bitwidth):" \
  "(sum-theoref)" \
  "(save-queries)(save-change-impact):" \
  "(tree-interpolants)(proof-trans):(reduce-proof)(reduce-proof-time):(reduce-proof-loops):(reduce-proof-graph):(color-proof):" \
  "(random-seed):(no-partitions)(no-itp)(verbose-solver):" \
  "(itp-algorithm): (itp-uf-algorithm): (itp-lra-algorithm):(itp-lra-factor): (check-itp): (part-itp):" \
  "(unwind):(unwindset):" \
  "(type-constraints):(type-byte-constraints):" \
  "(inlining-limit):(testclaim):" \
  "(pobj)(eq)(neq)(ineq)" \
  "(no-error-trace)" \
  "(list-templates)" \
  "(refine-mode):(init-mode):(logic):" \
  "(dump-query)(dump-pre-query)(dump-SSA-tree)(dump-query-name):" \
  "(partial-loops)"

class funfrog_parseoptionst:
  public parse_options_baset,
  public xml_interfacet,
  public messaget
{
public:
  virtual int doit();
  virtual void help();

  void ssos(){
    cbmc_status_interface("Partial Inlining");
  }
  funfrog_parseoptionst(int argc, const char **argv);

protected:
  goto_modelt goto_model;
  ui_message_handlert ui_message_handler; // KE: due to chnage from register_languages to messaget

  void register_languages();
  void get_command_line_options(optionst &);
  void set_default_options(optionst &);

  unsigned count(const goto_functionst &goto_functions) const;
  unsigned count(const goto_programt &goto_program) const;

  bool process_goto_program(const optionst &);
  bool get_goto_program(const optionst &);
  bool check_function_summarization();

 // unsigned long report_mem(void) const;
 // unsigned long report_max_mem(unsigned long mem) const;
  
  void set_options(const cmdlinet &cmdline);
  void eval_verbosity();

  optionst options;
  std::ofstream statfile;

private:
  void cbmc_error_interface(std::string error_msg) { error() << error_msg << eom; } // KE: adjust for CBMC 5.5 interface
  void cbmc_status_interface(std::string msg) { status() << msg << eom; } // KE: adjust for CBMC 5.5 interface
};

#endif
