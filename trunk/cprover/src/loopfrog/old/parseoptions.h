/*******************************************************************\

Module: Command Line Parsing

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_LOOPFROG_PARSEOPTIONS_H
#define CPROVER_LOOPFROG_PARSEOPTIONS_H

#include <langapi/language_ui.h>
#include <ui_message.h>
#include <parseoptions.h>

#define LOOPFROG_OPTIONS \
  "D:I:(16)(32)(64)(v):(binary):(version)(i386-linux)" \
  "(i386-macos)(ppc-macos)(i)"

class loopfrog_parseoptionst:
  public parseoptions_baset,
  public language_uit
{
public:
  virtual int doit();
  virtual void help();

  loopfrog_parseoptionst(int argc, const char **argv):
    parseoptions_baset(LOOPFROG_OPTIONS, argc, argv),
    language_uit(cmdline)
  {
  }
  
protected:
};

#endif
