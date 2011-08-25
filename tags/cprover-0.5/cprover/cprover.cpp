/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

/*

  CPROVER
  Copyright (C) 2000-2002 Daniel Kroening <kroening@handshake.de>

  Purpose: Main Module, Command Line Parsing

*/

#include <iostream>

#include <parseoptions.h>
#include <config.h>
#include <lispexpr.h>

#include "lang.h"

class parseoptionst:public parseoptions_baset
{
public:
  parseoptionst(int argc, const char **argv):
    parseoptions_baset("(parse)"
      "(lispexpr)(convert)(preprocess)", argc, argv)
  {
  }

  virtual int doit();
  virtual void help();
};

/*******************************************************************\

Function: parseoptionst::doit

  Inputs:

 Outputs:

 Purpose: invoke main modules

\*******************************************************************/

int parseoptionst::doit()
{
  config.set(cmdline);

  if(cmdline.isset("parse"))
    return parse_lang(cmdline);
  else if(cmdline.isset("preprocess"))
    return preprocess_lang(cmdline);
  else if(cmdline.isset("convert"))
    return convert_lang(cmdline);
  else if(cmdline.isset("lispexpr"))
    return test_lispexpr();
  else
    help();

  return 1;
}

/*******************************************************************\

Function: parseoptionst::help

  Inputs:

 Outputs:

 Purpose: display command line help

\*******************************************************************/

void parseoptionst::help()
{
  std::cout <<
    "\n"
    "* *    CPROVER - Copyright (C) 2000-2002 Daniel Kroening    * *\n"
    "* * Carnegie Mellon University, Computer Science Department * *\n"
    "* *                  kroening@cs.cmu.edu                    * *\n"
    "\n"
    "Usage:                       Purpose:\n"
    "\n"
    " cprover [-?] [-h] [--help]   show help\n"
    " cprover --preprocess file    preprocess\n"
    " cprover --parse file         parse\n"
    " cprover --convert file       convert\n"
    " cprover --lispexpr           parse lisp expressions (stdin)\n"
    "\n"
    "Additonal options:\n"
    "\n"
    "\n";
}

/*******************************************************************\

Function: main

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int main(int argc, const char **argv)
{
  parseoptionst parseoptions(argc, argv);
  return parseoptions.main();
}
