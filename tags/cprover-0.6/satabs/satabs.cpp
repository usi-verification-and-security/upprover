/*******************************************************************\

Module: CEGAR Main Module 

Authors: Daniel Kroening, kroening@kroening.com
         Karen Yorav

Date: June 2003

\*******************************************************************/

/*

  SATABS
  Counterexample Guided Abstraction Refinement for ANSI-C
  Copyright (C) 2003-2008 Daniel Kroening <kroening@kroening.com>

  Purpose: Main Module

*/

#include "cmdline_options.h"


#ifndef _WIN32

#include <stdlib.h>
#include <signal.h>

void xcpu_termination_handler(int signum)
{
  std::cout << std::endl << "TIME LIMIT EXCEEDED" << std::endl;
  exit(0);
}

#endif

/*******************************************************************\

Function: main

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
 
int main(int argc, const char **argv) 
{
  #ifndef _WIN32
  signal(SIGXCPU, &xcpu_termination_handler);
  #endif
  
  cmdline_optionst cmdline_options(argc, argv); 
  return cmdline_options.main();
}
