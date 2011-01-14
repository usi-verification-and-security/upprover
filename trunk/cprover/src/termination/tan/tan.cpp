/*******************************************************************\

 Module: Command Line Parsing

 Author: CM Wintersteiger

\*******************************************************************/

#include <sys/time.h>
#include <sys/stat.h>
#ifndef _WIN32
#include <sys/resource.h>
#else
#include <io.h>
#endif

#include <config.h>
#include <time_stopping.h>

#include <goto-programs/read_goto_binary.h>
#include <goto-programs/goto_inline.h>
#include <goto-programs/goto_function_pointers.h>
#include <goto-programs/remove_unused_functions.h>
#include <goto-programs/string_instrumentation.h>
#include <goto-programs/string_abstraction.h>
#include <goto-programs/set_claims.h>
#include <goto-programs/show_claims.h>

#include <satabs/prepare/prepare_functions.h>
#include <termination/instrumentation.h>
#include <termination/termination.h>
#include <termination/termination_slicer.h>

#include "tan.h"
#include "version.h"
#include "languages.h"

/*******************************************************************

 Function: tant::tant

 Inputs:

 Outputs:

 Purpose: constructor

 \*******************************************************************/

tant::tant(int argc, const char **argv):
  parseoptions_baset(TAN_OPTIONS, argc, argv),
  language_uit("TAN" TAN_VERSION, cmdline),
  ns(context),
  loops_nonterminating(0)
{
}

/*******************************************************************

 Function: tant::doit

 Inputs:

 Outputs:

 Purpose: invoke main modules

 \*******************************************************************/

int tant::doit()
{
  register_languages();

  if(check_and_set_options()) return TAN_UNKNOWN;
  if(from_file(cmdline.args[0])) return TAN_UNKNOWN;  
  if(preprocess()) return TAN_UNKNOWN;
  
  return analyze();  
}

/*******************************************************************\
  
 Function: tant::help

 Inputs:

 Outputs:

 Purpose: display command line help

 \*******************************************************************/

void tant::help()
{    
  std::cout <<"\n"
    "* * *                 TAN " TAN_VERSION
  " - Copyright (C) 2009               * * *\n"
  "              Daniel Kroening & Christoph M. Wintersteiger\n"
  "\n"
  "Usage:                         Purpose:\n"
  "\n"
  " tan [-?] [-h] [--help]        show help\n"
  " tan [options] <file>          run on goto-binary `file'\n"
  "\nDisplay options:\n"
  "--version                      show version information\n"
  "--v <int>                      set verbosity (default: 6)\n"
  "--show-model                   show the model as loaded\n"
  "--show-preprocessed-model      show the model after preprocessing\n"
  "--string-abstraction           enable string abstraction\n"
  "--no-invariant-propagation     disable invariant propagation\n"
  "--no-value-sets                disable value sets (pointer analysis)\n"
  "--function                     set entry point\n"
  "--claim #                      check only claim #\n"
  "--show-claims                  show all available claims\n"  
  "\nTermination Engine Options:\n"
  "--engine <engine>              Select one of the termination engines:\n"
  "          cta                  Compositional Termination Analysis (default)\n"
#ifdef HAVE_INTERPOLATION
  "          ita                  Interpolating Termination Analysis\n"
#endif
  "          enum                 Path Enumeration\n"
  "          bre                  Binary Reachability Engine\n"    
  "          direct               direct approach (Biere et al.)\n"  
  "--ranksynthesis <m>            choose rank synthesis method <m>:\n"
  "          sat                  SAT enumeration (default)\n"
  "          qbf                  QBF w/ unconstrained coefficients\n"
  "          qbfC                 QBF w/ constrained coefficients\n"
  "          rf                   Linear rank functions via Rankfinder\n"
  "          seneschal            Linear rank functions via Seneschal\n"
  "          qbfbA                QBF Bitwise affine functions\n"
  "          qbfbC                QBF Bitwise conjunctive functions\n"
  "          qbfbD                QBF Bitwise disjunctive functions\n"
  "          qbfbN                QBF Bitwise bottom (no functions)\n"
  "          qbfbP                QBF Bitwise projective functions\n"
  "          none                 No ranking functions\n"
  "--unranked-method <m>          how to react to unranked paths\n"
  "          none                 report the loop as non-terminating (default)\n"
  "          precondition         check reachability of wp(path) (using CEGAR)\n"
  "          bmc-precondition     check reachability of wp(path) (using BMC)\n"
  "          cegar                check loop reachability (using CEGAR)\n"
  "          bmc                  check loop reachability (using BMC)\n"
  "--no-loop-slicing              disable loop slicing (BRE and direct only)\n"  
  "\n";
}

/*******************************************************************\
  
 Function: tant::check_and_set_options

 Inputs:

 Outputs:

 Purpose: 

 \*******************************************************************/

bool tant::check_and_set_options(void)
{
  if (config.set(cmdline))
  {
    usage_error();
    return true;
  }

  if(cmdline.isset("version"))
  {
    std::cout << TAN_VERSION << std::endl;
    return true;
  }
    
  int verbosity=6;
  if(cmdline.isset("v")) verbosity=atoi(cmdline.getval("v"));
  set_verbosity(verbosity);
  
  if(cmdline.args.size()==0)
  {
    error("Please provide an input file.");
    return 1;
  }
  else if (cmdline.args.size()>1)
  {
    error("Multiple input files not supported.");
    return 1;
  }
  
  std::string engine="cta";
  if(cmdline.isset("engine"))
    engine=cmdline.getval("engine");
  
  if(cmdline.isset("no-loop-slicing") &&
     engine!="direct" && engine!="bre")
    warning("Warning: --no-loop-slicing is only available "
            "with the following engines: bre, direct.");
  
  if(cmdline.isset("unranked-method"))
  {
    std::string u_mode=cmdline.getval("unranked-method");
    if(u_mode!="none" && u_mode!="precondition" && u_mode!="bmc-precondition" &&
        u_mode!="cegar" && u_mode!="bmc")
      warning("Warning: unknown unranked-method.");    
  }  
  
  return false;
}


/*******************************************************************\
  
 Function: tant::from_file

 Inputs:

 Outputs:

 Purpose: 

 \*******************************************************************/

bool tant::from_file(const std::string &filename)
{  
  std::ifstream infile(filename.c_str());
  if (!infile)
  {
    error(std::string("Error opening file `")+filename+"'.");
    return true;
  }  

  status(std::string("Loading `")+filename+"' ...");
  if(read_goto_binary(filename, context, goto_functions, get_message_handler()))
  {
    error(std::string("Error reading file `")+filename+"'.");
    return true;
  }
  
  if(cmdline.isset("show-program"))
  {
    goto_functions.output(namespacet(context), std::cout);
    return true;    
  }
  
  return false;
}

/*******************************************************************\
  
 Function: tant::preprocess

 Inputs:

 Outputs:

 Purpose: 

 \*******************************************************************/

bool tant::preprocess(void)
{
  message_handlert &mh=get_message_handler();
  
  if(cmdline.isset("show-model"))
  {
    goto_functions.output(ns, std::cout);
    return true;
  }
  
  if(cmdline.isset("string-abstraction"))
    string_instrumentation(context, mh, goto_functions);
  
  status("Removing function pointers");
  remove_function_pointers(goto_functions);

  status("Removing unused functions");
  remove_unused_functions(goto_functions, mh);
  
  status("Partial inlining");
  goto_partial_inline(goto_functions, ns, mh);
  
  // we do this again, to remove all the functions that are inlined now
  remove_unused_functions(goto_functions, mh);

  status("Adjusting functions");
  prepare_functions(context, goto_functions, mh);
  
  if(cmdline.isset("string-abstraction"))
  {
    status("String Abstraction");
    string_abstraction(context, mh, goto_functions);
  }
    
  goto_functions.compute_location_numbers();
  
  status("Termination instrumentation");
  termination_instrumentert::modet instrumenter_mode=
    termination_instrumentert::T_RANKSYNTH;
    
  if(cmdline.isset("engine") &&
     cmdline.getval("engine")==std::string("direct"))
  {
    if(cmdline.isset("ranksynthesis"))
        warning("Warning: --ranksynthesis does not make sense with --direct.");

    instrumenter_mode = termination_instrumentert::T_DIRECT;
  }

  termination_instrumentert termination(goto_functions, context, mh, instrumenter_mode);
  termination.set_verbosity(verbosity);
  unsigned loopcount=termination.instrument();
  goto_functions.update();
    
  if(cmdline.isset("show-claims"))
  {
    if(loopcount==0)
      std::cout << "No claims." << std::endl; 
    else
      show_claims(ns, ui_message_handlert::PLAIN, goto_functions);
    
    return true;
  }
  
  if(!cmdline.isset("no-invariant-propagation"))
  {
    fine_timet before=current_time();
    
    // This is done without value_set_analysis being initialized
    value_set_analysist vsa(ns);
    invariant_propagationt ip(ns, vsa);
        
    status("Invariant Propagation");
    
    try 
    {
      ip(goto_functions);    
  
      if(cmdline.isset("show-invariant-sets"))
      {
        ip.output(goto_functions, std::cout);
        return true;
      }
    
      ip.simplify(goto_functions);
      ip.clear();
    }
    catch (const std::bad_alloc &e) 
    {
      ip.clear();
      
      warning("Warning: Invariant propagation canceled because it "
              "exceeded the memory limit");
    }
    
    status("Invariant Propagation: " + 
           time2string(current_time()-before) + " s total.");
  }

  // set claim
  if(cmdline.isset("claim"))
    set_claims(goto_functions, cmdline.get_values("claim"));
  
  
  if(cmdline.isset("show-preprocessed-model"))
  {
    goto_functions.output(ns, std::cout);
    return true;
  }
  
  return false;
}

/*******************************************************************\
  
 Function: tant::analyze

 Inputs:

 Outputs:

 Purpose: 

 \*******************************************************************/

tan_resultt tant::analyze(void)
{  
  contextt shadow_context;
  value_set_analysist value_set_analysis(ns);
  invariant_propagationt invariant_propagation(ns, value_set_analysis);
  
  std::vector<exprt> up_predicates;
  unsigned int max_iterations=0;
  
  termination_prover_modet engine=TP_COMPOSITIONAL;
  
  if(cmdline.isset("engine"))
  {
    std::string estr=cmdline.getval("engine");
    
    if(estr=="bre") engine=TP_BINARY_REACHABILITY;
    else if(estr=="direct") engine=TP_DIRECT;
    else if(estr=="enum") engine=TP_PATH_ENUMERATION;
    else if(estr=="cta") engine=TP_COMPOSITIONAL;
#ifdef HAVE_INTERPOLATION
    else if(estr=="ita") engine=TP_INTERPOLATING;
#endif
    else throw ("Unknown termination engine selected");
  }
  
  termination_resultt
    res=termination(engine,
                    cmdline, goto_functions, context, shadow_context, 
                    value_set_analysis, invariant_propagation, *message_handler,
                    ui_message_handlert::PLAIN,
                    up_predicates, max_iterations);
  
  switch(res)
  {
    case T_TERMINATING: return TAN_TERMINATING;
    case T_NONTERMINATING: return TAN_NONTERMINATING;
    default: return TAN_ERROR;
  }  
}
