/*******************************************************************\

Module: Command Line Parsing

Author: Daniel Kroening, kroening@kroening.com
        CM Wintersteiger
        Ondrej Sery

\*******************************************************************/

#ifndef CPROVER_FUNFROG_PARSEOPTIONS_H
#define CPROVER_FUNFROG_PARSEOPTIONS_H

#include <fstream>
#include <langapi/language_ui.h>
#include <ui_message.h>
#include <parseoptions.h>
#include <options.h>

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
  "(show-symbol-table)(save-stats)(show-value-sets)" \
  "(save-claims)" \
  "(no-slicing)(no-assert-grouping)" \
  "(pointer-check)(bounds-check)(assertions)(use-smt)" \
  "(show-pass)(suppress-fail)(no-progress)" \
  "(save-summaries)(show-claims)(claim):" \
  "(save-queries)" \
  "(reduce-proof):(verbose-solver):" \
  "(unwind):(unwindset):" \
  "(inlining-limit):(testclaim):" \
  "(pobj)(eq)(neq)(ineq)"
class funfrog_parseoptionst:
  public parseoptions_baset,
  public language_uit
{
public:
  virtual int doit();
  virtual void help();

  funfrog_parseoptionst(int argc, const char **argv);

protected:
  unsigned count(const goto_functionst &goto_functions) const;
  unsigned count(const goto_programt &goto_program) const;

  bool check_loop_summarization(namespacet &ns,
                                value_set_alloc_adaptort &adaptor,
                                goto_functionst &goto_functions,
                                std::string &stats_dir);

  unsigned long report_mem(void) const;
  unsigned long report_max_mem(unsigned long mem) const;
  
  void set_options(const cmdlinet &cmdline);

  optionst options;
  std::ofstream statfile;
};

#endif
