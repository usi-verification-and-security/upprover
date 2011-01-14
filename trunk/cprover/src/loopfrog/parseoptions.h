/*******************************************************************\

Module: Command Line Parsing

Author: Daniel Kroening, kroening@kroening.com
        CM Wintersteiger

\*******************************************************************/

#ifndef CPROVER_LOOPFROG_PARSEOPTIONS_H
#define CPROVER_LOOPFROG_PARSEOPTIONS_H

#include <fstream>
#include <langapi/language_ui.h>
#include <ui_message.h>
#include <parseoptions.h>
#include <options.h>

#include <goto-programs/goto_functions.h>
#include <pointer-analysis/value_sets.h>
#include "loopstore.h"

class value_set_alloc_adaptort;

#define LOOPFROG_OPTIONS \
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
  "(show-symbol-table)(save-stats)(show-value-sets)" \
  "(save-claims)(save-loops)(ag-reasoning)" \
  "(pointer-check)(bounds-check)(assertions)(use-smt)" \
  "(show-pass)(suppress-fail)(no-progress)" \
  "(save-summaries)(show-claims)(claim):" \
  "(inlining-limit):(testclaim):(incremental)(interactive)" \
  "(no-invariants)(zt)(ib)(i2)(sb)(sl)(dl)(ct)(np)(poff)" \
  "(check-by-invariant-propagation)" \
  "(pobj)(eq)(neq)(ineq)" \
  "(termination)(no-claim-check)(ti1)(ti2)(ti3)(ti4)(ti5)(st1)(st2)"
class loopfrog_parseoptionst:
  public parseoptions_baset,
  public language_uit
{
public:
  virtual int doit();
  virtual void help();

  loopfrog_parseoptionst(int argc, const char **argv);

protected:
  unsigned count(const goto_functionst &goto_functions) const;
  unsigned count(const goto_programt &goto_program) const;
  unsigned count(
    const goto_functionst &goto_functions,
    const loopstoret &imprecise_summaries,
    const loopstoret &precise_summaries,
    unsigned add) const;

  unsigned long report_mem(void) const;
  unsigned long report_max_mem(unsigned long mem) const;
  
  bool check_invariant_propagation(namespacet &ns,
                                   value_set_alloc_adaptort &adaptor,
                                   goto_functionst &goto_functions);
  
  bool check_loop_summarization(namespacet &ns,
                                value_set_alloc_adaptort &adaptor,
                                goto_functionst &goto_functions,
                                std::string &stats_dir);
  
  void set_options(const cmdlinet &cmdline);

  optionst options;
  std::ofstream statfile;
};

#endif
