/*******************************************************************\

Module: Main Module 

Author: Daniel Kroening, kroening@kroening.com
        CM Wintersteiger

\*******************************************************************/

#include <config.h>

#include <iostream>
#include <fstream>

#include <message.h>
#include <context.h>
#include <i2string.h>

#include <goto-programs/read_goto_binary.h>
#include <goto-programs/goto_functions.h>
#include <goto-programs/goto_convert_functions.h>

#include <pointer-analysis/value_propagation_fivr.h>

#include <time_stopping.h>

#include "version.h"
#include "loop_classifier.h"
#include "parseoptions.h"

/*******************************************************************\

Function: loopfrog_parseoptionst::doit

  Inputs:

 Outputs:

 Purpose: invoke main modules

\*******************************************************************/

int loopfrog_parseoptionst::doit()
{
  if(config.set(cmdline))
  {
    usage_error();
    exit(1);
  }
  
  stream_message_handlert mh(std::cout);
  set_message_handler(&mh);

  int verbosity=6;
  if (cmdline.isset("v"))
  {
    verbosity=atoi(cmdline.getval("v"));
    set_verbosity(verbosity);
  }

  if (cmdline.args.size()==0)
  {
    error("Please provide an input file.");
    return 1;
  }
  else if (cmdline.args.size()>1)
  {
    error("Multiple input files not supported.");
    return 1;
  }

  std::ifstream infile(cmdline.args[0].c_str());
  if (!infile)
  {
    error(std::string("Error opening file `")+cmdline.args[0]+"'.");
    return 1;
  }

  contextt context;
  goto_functionst goto_functions;

  status(std::string("Loading `")+cmdline.args[0]+"' ...");
  read_goto_binary(infile, context, goto_functions, *message_handler);  
  
  //status("Removing function pointers...");
  //nul_message_handlert temp;
  //remove_function_pointers(context, optionst(), goto_functions, temp);

  status("Value set propagation...");
  namespacet ns(context); fine_timet before,after;  
  before=current_time();
  value_propagation_fivrt value_propagation(ns);
  value_propagation(goto_functions);
  after=current_time();
  status(std::string("VSP Time: ") + time2string(after-before) + " sec.");
  
  goto_functionst::function_mapt::const_iterator pit = 
    goto_functions.function_map.find("c::main");
  if (pit==goto_functions.function_map.end()) 
  {
    error("c::main not found.");
    return 1;
  }    
//  value_propagation.output(pit->second.body, std::cout);
    
  if (cmdline.isset("i"))
  {
    status("Instrumenting...");
    loop_classifiert loop_classifier(value_propagation);
    loop_classifier.instrument( context, goto_functions );
  }
  else
  {
    status("Classifying...");
    loop_classifiert loop_classifier(value_propagation);
    loop_classifier.classify( context, goto_functions );
  }
  
  status("Done.\n");

  return 0;
}

/*******************************************************************\

Function: loopfrog_parseoptionst::help

  Inputs:

 Outputs:

 Purpose: display command line help

\*******************************************************************/

void loopfrog_parseoptionst::help()
{
  std::cout <<
    "\n"
    "* *         LOOPFROG " LOOPFROG_VERSION 
    " - Copyright (C) 2007           * *\n"
    "\n"
    "Usage:                       Purpose:\n"
    "\n"
    " loopfrog [-?] [-h] [--help]  show help\n"
    " loopfrog file                binary file name\n"
    "\n"
    "Additonal options:\n"
    "--v <int>                     set verbosity (default=6)\n"
    "--i                           instrument program\n"
    "\n";
}
