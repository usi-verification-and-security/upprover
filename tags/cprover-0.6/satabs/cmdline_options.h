/*******************************************************************\

Module: Parse Command Line Options for CEGAR

Author: Daniel Kroening
        Karen Yorav

Date: June 2003

\*******************************************************************/

#ifndef CPROVER_CEGAR_CMDLINE_OPTIONS_H
#define CPROVER_CEGAR_CMDLINE_OPTIONS_H

#include <parseoptions.h>
#include <config.h>

#include <cbmc/xml_interface.h>

class cmdline_optionst:
  public parseoptions_baset,
  public xml_interfacet
{
public:
  virtual int doit();
  virtual void help();

  cmdline_optionst(int argc, const char **argv):
    parseoptions_baset("(v):(gui)(show-loops)"
    "(16)(32)(64)(LP64)(ILP64)(LLP64)(ILP32)(LP32)" \
    "(show-final-program)(show-basic-blocks)(modelchecker):"
    "(show-dereferenced-program)(string-abstraction)"
    "(string-abstraction)(full-inlining)"
    "(predicates):(show-claims)(bounds-check)(no-library)"
    "(no-invariant-sets)(no-value-sets)(module):"
    "(xml-ui)(xml-interface)"
    "(show-equations)(show-value-sets)(show-invariant-sets)"
    "(div-by-zero-check)(pointer-check)"
    "(no-assertions)(no-assumptions)"
    "(iterations):(function):(initial-state):(show-last-trace)"
    "(show-adjusted-functions)(no-simplify)(refiner):(ipplimit):"
    "(show-goto-functions)(overflow-check)(simulator):"
    "(abstractor):I:D:(claim):(little-endian)(big-endian)"
    "(property):(module):(loop-detection)(no-slicing)"
    "(data-race-check)(error-label):(prefix-first)(no-arch)"
    "(binary):(no-path-slicing)(version)(shortest-prefix)"
    "(termination)(ranksynthesis):(no-loop-slicing)"
    "(save-bps)(max-threads)",
    argc, argv),
    xml_interfacet(cmdline)
  {
  }
};

#endif
