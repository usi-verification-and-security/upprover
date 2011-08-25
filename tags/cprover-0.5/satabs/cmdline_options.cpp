/*******************************************************************\

Module: Parsing Command Line Options for CEGAR

Author: Daniel Kroening
        Karen Yorav

Date: June 2003

\*******************************************************************/

#include <iostream>
#include <memory>

#include <message.h>

#include <goto-symex/xml_goto_trace.h>

#include <cbmc/xml_interface.h>

#include "cmdline_options.h"
#include "satabs_safety_checker.h"
#include "safety.h"
#include "version.h"

#include "modelchecker/select_modelchecker.h"
#include "simulator/select_simulator.h"
#include "refiner/select_refiner.h"
#include "prepare/prepare.h"
#include "abstractor/select_abstractor.h"

/*******************************************************************\

Function: cmdline_optionst::doit

  Inputs:

 Outputs:

 Purpose: Parse and store options

\*******************************************************************/

int cmdline_optionst::doit()
{
  if(cmdline.isset("version"))
  {
    std::cout << SATABS_VERSION << std::endl;
    return 0;
  }
  
  optionst options;

  options.set_option("bounds-check", cmdline.isset("bounds-check"));
  options.set_option("div-by-zero-check", cmdline.isset("div-by-zero-check"));
  options.set_option("pointer-check", cmdline.isset("pointer-check"));
  options.set_option("assertions", !cmdline.isset("no-assertions"));
  options.set_option("assumptions", !cmdline.isset("no-assumptions"));
  options.set_option("simplify", !cmdline.isset("no-simplify"));
  options.set_option("overflow-check", cmdline.isset("overflow-check"));

  if(cmdline.isset("error-label"))
    options.set_option("error-label", cmdline.getval("error-label"));

  // context that can be changed within the CEGAR loop
  contextt shadow_context;

  preparet prepare(cmdline, options, shadow_context);

  message_handlert &message_handler=prepare.ui_message_handler;

  // set the same verbosity for all
  int verbosity=6;
  if(cmdline.isset("v"))
    verbosity=atoi(cmdline.getval("v"));

  prepare.set_verbosity(verbosity);

  // get configuration

  config.set(cmdline);

  // Parse input program, convert to goto program

  if(prepare.doit())
    return 1;  

  try
  {
    messaget message(message_handler);
  
    concrete_modelt concrete_model(prepare.ns, prepare.goto_functions);

    loop_componentt::argst args(
      message_handler, concrete_model);
    
    // The tools we need

    // finds predicates
    std::auto_ptr<refinert> refiner(
      select_refiner(cmdline, args));

    // calculates abstract program
    std::auto_ptr<abstractort> abstractor(
      select_abstractor(cmdline, args));

    // model checking engine
    std::auto_ptr<modelcheckert> modelchecker(
      select_modelchecker(cmdline, args));

    // simulator
    std::auto_ptr<simulatort> simulator(
      select_simulator(cmdline, args, prepare.shadow_context));
    
    // set their verbosity -- all the same for now
    refiner->set_verbosity(verbosity);
    abstractor->set_verbosity(verbosity);
    modelchecker->set_verbosity(verbosity);
    simulator->set_verbosity(verbosity);    
    
    satabs_safety_checkert satabs_safety_checker(
      prepare.ns,
      *abstractor,
      *refiner,
      *modelchecker,
      *simulator);
    
    satabs_safety_checker.initial_predicates=
      prepare.user_provided_predicates;
      
    satabs_safety_checker.set_message_handler(message_handler);
    satabs_safety_checker.ui=prepare.get_ui();    
    satabs_safety_checker.max_iterations=prepare.max_iterations();
    satabs_safety_checker.save_bps=cmdline.isset("save-bps");    
    satabs_safety_checker.set_verbosity(verbosity);
        
    switch(satabs_safety_checker(prepare.goto_functions))
    {
    case safety_checkert::SAFE:
      message.result("VERIFICATION SUCCESSFUL");

      if(prepare.get_ui()==ui_message_handlert::XML_UI)
      {
        xmlt xml("cprover-status");
        xml.data="SUCCESS";
        std::cout << xml << std::endl;
      }

      return 0;
    
    case safety_checkert::UNSAFE:
      if(prepare.get_ui()==ui_message_handlert::XML_UI)
      {
        xmlt xml1;
        convert(concrete_model.ns, satabs_safety_checker.error_trace, xml1);
        std::cout << xml1 << std::endl;

        xmlt xml2("cprover-status");
        xml2.data="FAILURE";
        std::cout << xml2 << std::endl;
      }
      else
      {
        message.result("Counterexample:");
        pretty_namest pretty_names;
        show_goto_trace(std::cout, concrete_model.ns,
                        pretty_names, satabs_safety_checker.error_trace);
        message.result("VERIFICATION FAILED");
      }

      return 10;
    
    case safety_checkert::ERROR:
    default:;
      return 12;
    }
  }

  catch(const char *e)
  {
    prepare.error(e);
    return 1;
  }

  catch(const std::string e)
  {
    prepare.error(e);
    return 1;
  }
  
  catch(std::bad_alloc)
  {
    prepare.error("Out of memory");
    return 100;
  }

  return 0;
}

/*******************************************************************\

Function: cmdline_optionst::help

  Inputs:

 Outputs:

 Purpose: display command line help

\*******************************************************************/

void cmdline_optionst::help()
{
  std::cout <<
    "\n"
    "* *          SATABS " SATABS_VERSION " - Copyright (C) 2003-2006           * *\n"
    "* *              Daniel Kroening, Edmund Clarke             * *\n"
    "* *         Computer Systems Institute, ETH Zurich          * *\n"
    "* *                 kroening@kroening.com                   * *\n"
    "* *        Protected in part by U.S. patent 7,418,680       * *\n"
    "\n"
    "Usage:                       Purpose:\n"
    "\n"
    " satabs [-?] [-h] [--help]    show help\n"
    " satabs source.c              check given program\n"
    "\n"
    "Frontend options:\n"
    " --binary name                check a goto-cc binary\n"
    " -I path                      set include path (C/C++)\n"
    " -D macro                     define preprocessor macro (C/C++)\n"
    " --16, --32, --64             Set width of machine word\n"
    " --LP64, --ILP64, --LLP64,\n"
    "   --ILP32, --LP32            set width of int, long and pointers\n"
    " --little-endian              Allow little-endian word-byte conversions\n"
    " --big-endian                 Allow big-endian word-byte conversions\n"
    " --function name              set main function name\n"
    " --full-inlining              perform full inlining\n"
    " --show-goto-functions        just show goto program\n"
    " --show-basic-blocks          just show the basic blocks program\n"
    " --show-equations             just show the equations\n"
    " --show-loops                 just show the loops\n"
    " --show-value-sets            just show the value set propagation\n"
    " --show-invariant-sets        just show the invariant set propagation\n"
    "\n"
    "Instrumentation options:\n"
    " --no-assertions              ignore user assertions\n"
    " --no-assumptions             ignore user assumptions\n"
    " --bounds-check               enable array bounds checks\n"
    " --div-by-zero-check          enable division by zero checks\n"
    " --pointer-check              enable pointer checks\n"
    " --overflow-check             enable overflow checks\n"
    " --data-race-check            enable data race checks\n"
    " --error-label label          check that label is unreachable\n"
    " --show-claims                just show the claims\n"
    "\n"
    "Modelchecker options:\n"
    " --claim #                    check a specific claim only\n"
    " --loop-detection             use heuristic to detect loops\n"
    " --modelchecker name          set the modelchecker to be used\n"
    " --abstractor name            set the abstractor to be used\n"
    " --refiner name               set the refiner to be used\n"
    " --iterations #               set maximum number of refinement iterations\n"
    " --predicates file            read predicates from file\n"
    " --no-path-slicing            disable path slicer\n"
    " --save-bps                   save a Boolean program for each iteration\n"
    "\n"
    "Other options:\n"
    " --v #                        verbosity level\n"
    "\n";
}
