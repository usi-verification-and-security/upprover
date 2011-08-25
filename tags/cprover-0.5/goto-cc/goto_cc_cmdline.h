/*******************************************************************\

Module: Command line interpretation for goto-cc

Author: Daniel Kroening

Date:   April 2010

\*******************************************************************/

#ifndef GOTO_CC_CMDLINE_H
#define GOTO_CC_CMDLINE_H

#include <cmdline.h>

class goto_cc_cmdlinet:public cmdlinet
{
public:
  typedef enum { MS, GCC } modet;
  modet mode;

  virtual bool parse(int argc, const char **argv)=0;
};

#endif /*CMDLINE_H_*/
