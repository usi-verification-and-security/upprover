/*******************************************************************\

Module: Command Line Parsing

Author: Daniel Kroening, kroening@kroening.com
        CM Wintersteiger
        Ondrej Sery

\*******************************************************************/

#ifndef CPROVER_FUNFROG_PARSEOPTIONS_H
#define CPROVER_FUNFROG_PARSEOPTIONS_H

#include <fstream>
#include <iostream>
#include <langapi/language_ui.h>
#include <options.h>
#include "xml_interface.h"

#include <util/ui_message.h>
#include <util/parseoptions.h>

#include <goto-programs/goto_functions.h>
#include <pointer-analysis/value_sets.h>

class value_set_alloc_adaptort;

#define FUNFROG_OPTIONS \
  "D:I:(16)(32)(64)(v):(version)" \
  "(i386-linux)(i386-macos)(ppc-macos)" \
  "(show-leaping-program)(show-instrumented-program)" \
  "(save-leaping-program)(save-instrumented-program)" \
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
  "(init-upgrade-check)(do-upgrade-check):" \
  "(no-slicing)(no-assert-grouping)(no-summary-optimization)" \
  "(pointer-check)(bounds-check)(div-by-zero-check)(overflow-check)(nan-check)" \
  "(string-abstraction)(assertions)" \
  "(show-pass)(suppress-fail)(no-progress)" \
  "(show-claims)(all-claims)(claims-order):(claim):(claimset):" \
  "(save-queries)(save-change-impact):" \
  "(tree-interpolants)(proof-trans):(reduce-proof-time):(reduce-proof-loops):(reduce-proof-graph):(color-proof):" \
  "(random-seed):(no-itp)(verbose-solver):" \
  "(itp-algorithm): (check-itp)" \
  "(unwind):(unwindset):" \
  "(inlining-limit):(testclaim):" \
  "(pobj)(eq)(neq)(ineq)" \
  "(refine-mode):(init-mode):"
class funfrog_parseoptionst:
  public parseoptions_baset,
  public xml_interfacet,
  public language_uit
{
public:
  virtual int doit();
  virtual void help();
  virtual void register_languages();

  void ssos(){
	  status("Partial Inlining");
  }
  funfrog_parseoptionst(int argc, const char **argv);

protected:
  unsigned count(const goto_functionst &goto_functions) const;
  unsigned count(const goto_programt &goto_program) const;

  bool process_goto_program(
    namespacet& ns,
    optionst& options,
    goto_functionst &goto_functions);
  bool get_goto_program(
    const std::string &filename,
    namespacet& ns,
    optionst& options,
    goto_functionst &goto_functions);
  bool check_function_summarization(namespacet &ns,
                                goto_functionst &goto_functions);

 // unsigned long report_mem(void) const;
 // unsigned long report_max_mem(unsigned long mem) const;
  
  void set_options(const cmdlinet &cmdline);

  optionst options;
  std::ofstream statfile;
};

#endif
