/*******************************************************************\

 Module: Command Line Parsing

 Author: Daniel Kroening, kroening@kroening.com
         CM Wintersteiger
         Ondrej Sery

\*******************************************************************/

#include <config.h>

#include <iostream>
#include <fstream>

#include <sys/time.h>
#include <sys/stat.h>
#ifndef _WIN32
#include <sys/resource.h>
#else
#include <io.h>
#endif

#include <i2string.h>
#include <std_expr.h>
#include <arith_tools.h>
#include <prefix.h>
#include <time_stopping.h>

#include <goto-programs/goto_convert_functions.h>
#include <goto-programs/remove_function_pointers.h>
#include <goto-programs/goto_inline.h>
#include <goto-programs/show_claims.h>
#include <goto-programs/set_claims.h>
#include <goto-programs/read_goto_binary.h>
#include <goto-programs/interpreter.h>
#include <goto-programs/string_abstraction.h>
#include <goto-programs/string_instrumentation.h>
#include <goto-programs/loop_ids.h>
#include <goto-programs/link_to_library.h>

#include <pointer-analysis/goto_program_dereference.h>
#include <pointer-analysis/add_failed_symbols.h>

#include <analyses/goto_check.h>
#include <langapi/mode.h>

#include "check_claims.h"
#include "upgrade_checker.h"
#include "version.h"
#include "parseoptions.h"


/*******************************************************************

 Function: funfrog_parseoptionst::funfrog_parseoptionst

 Inputs:

 Outputs:

 Purpose: constructor

 \*******************************************************************/

funfrog_parseoptionst::funfrog_parseoptionst(int argc, const char **argv):
  parseoptions_baset(FUNFROG_OPTIONS, argc, argv),
  xml_interfacet(cmdline),
  language_uit("FUNFROG" FUNFROG_VERSION, cmdline)
{
}

bool funfrog_parseoptionst::process_goto_program(
  namespacet& ns,
  optionst& options,
  goto_functionst &goto_functions)
{
  try
  {
   if(cmdline.isset("string-abstraction"))
      string_instrumentation(
        symbol_table, get_message_handler(), goto_functions);

    status("Function Pointer Removal");
    remove_function_pointers(symbol_table, goto_functions,
      cmdline.isset("pointer-check"));

    status("Partial Inlining");
    // do partial inlining
    goto_partial_inline(goto_functions, ns, ui_message_handler);

    status("Generic Property Instrumentation");
    // add generic checks
    goto_check(ns, options, goto_functions);

    if(cmdline.isset("string-abstraction"))
    {
      status("String Abstraction");
      string_abstraction(symbol_table,
        get_message_handler(), goto_functions);
    }

    // add failed symbols
    // needs to be done before pointer analysis
    add_failed_symbols(symbol_table);

    // recalculate numbers, etc.
    goto_functions.update();

    // add loop ids
    goto_functions.compute_loop_numbers();
  }

  catch(const char *e)
  {
    error(e);
    return true;
  }

  catch(const std::string e)
  {
    error(e);
    return true;
  }

  catch(int)
  {
    return true;
  }

  catch(std::bad_alloc)
  {
    error("Out of memory");
    return true;
  }

  return false;
}

bool funfrog_parseoptionst::get_goto_program(
  const std::string &filename,
  namespacet& ns,
  optionst& options,
  goto_functionst &goto_functions)
{
  if(cmdline.args.size()==0)
  {
    error("Please provide a program to verify");
    return true;
  }

  try
  {
    if(cmdline.args.size()==1 &&
       is_goto_binary(filename))
    {
      status("Reading GOTO program from file");

      if(read_goto_binary(filename,
           symbol_table, goto_functions, get_message_handler()))
        return true;

      config.ansi_c.set_from_symbol_table(symbol_table);

      if(symbol_table.symbols.find(ID_main)==symbol_table.symbols.end())
      {
        error("The goto binary has no entry point; please complete linking");
        return true;
      }
    }
    else
    {
      if(parse()) return true;
      if(typecheck()) return true;
      if(final()) return true;

      // we no longer need any parse trees or language files
      clear_parse();

      if(symbol_table.symbols.find(ID_main)==symbol_table.symbols.end())
      {
        error("No entry point; please provide a main function");
        return true;
      }

      status("Generating GOTO Program");

      goto_convert(symbol_table, goto_functions, ui_message_handler);

    }

    // finally add the library
    status() << "Adding CPROVER library" << eom;
    link_to_library(symbol_table, goto_functions, ui_message_handler);

    if(process_goto_program(ns, options, goto_functions))
      return true;
  }

  catch(const char *e)
  {
    error(e);
    return true;
  }

  catch(const std::string e)
  {
    error(e);
    return true;
  }

  catch(int)
  {
    return true;
  }

  catch(std::bad_alloc)
  {
    error("Out of memory");
    return true;
  }

  return false;
}
/*******************************************************************

 Function: funfrog_parseoptionst::doit

 Inputs:

 Outputs:

 Purpose: invoke main modules

 \*******************************************************************/

int funfrog_parseoptionst::doit()
{
  if (config.set(cmdline))
  {
    usage_error();
    exit(1);
  }

  if(cmdline.isset("version"))
  {
    std::cout << FUNFROG_VERSION << std::endl;
    return 1;
  }
  
  register_languages();
  set_options(cmdline);  
  
  //stream_message_handlert mh(std::cout);
  set_message_handler(ui_message_handler);

  int verbosity=6;
  if(cmdline.isset("v"))
  {
    verbosity=atoi(cmdline.getval("v"));
    set_verbosity(verbosity);
  }

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

  std::ifstream infile(cmdline.args[0].c_str());
  if (!infile)
  {
    error(std::string("Error opening file `")+cmdline.args[0]+"'.");
    return 1;
  }

  goto_functionst goto_functions;
  namespacet ns(symbol_table);
  fine_timet before, after;

  status(std::string("Loading `")+cmdline.args[0]+"' ...");
  before=current_time();
  
  if(get_goto_program(cmdline.args[0], ns, options, goto_functions))
    return 6;

  after=current_time();
  status() << "    LOAD Time: " << (after-before) << " sec." << eom;


  label_claims(goto_functions);

  if (cmdline.isset("show-symbol-table"))
  {
    show_symbol_table();
    return true;
  }

  if(cmdline.isset("show-program"))
  {
    goto_functions.output(ns, std::cout);
    return true;
  }

//  if (cmdline.isset("reduce-proof-graph") && cmdline.isset("reduce-proof-time")){
//    status("Please set either ratio or time for reduction or number of proof traversals.");
//    return false;
//  }

  if(check_function_summarization(ns, goto_functions))
    return 1;


  status("#X: Done.");

  return 0;
}

/*******************************************************************\
  
 Function: funfrog_parseoptionst::help

 Inputs:

 Outputs:

 Purpose: display command line help

 \*******************************************************************/

void funfrog_parseoptionst::help()
{
  std::cout <<"\n"
    "* * *                eVolCheck "EVOLCHECK_VERSION
    " - Copyright (C) 2012               * * *\n"
    "          Ondrej Sery, Grigory Fedyukovich & Natasha Sharygina\n\n"
    "                based on FUNFROG "FUNFROG_VERSION
    " - Copyright (C) 2011               * * *\n"
    "          Ondrej Sery, Grigory Fedyukovich & Natasha Sharygina\n\n"
  "\n"
  "Usage:                         Purpose:\n"
  "\n"
  " evolcheck [-?] [-h] [--help]    show help\n"
  " evolcheck [options] <file>      run on goto-binary `file'\n"
  "\nDisplay options:\n"
  "--version                      show version information\n"
  "--show-symbol-table            show symbol table\n"
  "--show-program                 show goto program (as loaded)\n"
  "--show-*-program               show intermediate program, where\n"
  "                               * is one of transformed, inlined,\n"
  "                               fpfreed, instrumented, claimed,\n"
  "                               abstracted, dereferenced, leaping\n"
  "--save-*-program               like --show-*-program, but save the\n"
  "                               program to goto_program_*\n"
  "--save-summaries <filename>    save collected function summaries\n"
  "                               to the given file\n"
  "--load-summaries <filename>    load function summaries\n"
  "                               from the given file\n"
  "--save-omega <filename>        save the last used substitution scenario\n"
  "                               to the given file\n"
  "--load-omega <filename>        load substitution scenario\n"
  "                               from the given file\n"
  "--no-progress                  turn off progress display\n"
  "--save-queries                 save SAT queries and configuration\n"
  "\nUpgrade options:\n"
  "--init-upgrade-check           prepare for upgrade checking\n"
  "--do-upgrade-check <filename>  incremental upgrade check with the specified\n"
  "                               upgraded version (goto-binary)\n"
  "--save-change-impact <xml>     save call-tree representing the change impact in xml file\n"
  "                               (by default in __calltree.xml)\n"
  "\nProof Engine options:\n"
  "--show-claims                  output the claims list\n"
  "--show-pass                    report passed claims\n"
  "--suppress-fail                don't report failed claims\n"
  "--save-claims                  save claim info in `file'_data/claim*\n"
  "--bounds-check                 enable array bounds checks\n"
  "--div-by-zero-check            enable division by zero checks\n"
  "--pointer-check                enable pointer checks\n"
  "--overflow-check               enable arithmetic over- and underflow checks\n"
  "--nan-check                    check floating-point for NaN\n"
  "--assertions                   add user supplied assertions\n"
  "--claim <int>                  check a specific claim\n"
  "--claimset <int,int,...>       check specific claims separated by comas\n"
  "--all-claims                   check all claims in one run\n"
  "--claims-order <fraction>      find the strongest claims using the given treshold\n"
  "                               treshold = 1/<fraction> of SSA steps\n"
  "--unwind <bound>               loop unwind bound\n"
  "--unwindset <label:bound,...>  set of loop unwind bound for specific\n"
  "                               loops\n"
  "--no-slicing                   no slicing of the SSA program form (slower\n"
  "                               computation, more dependable result)\n"
  "--no-assert-grouping           do not group checks for the same assertion\n"
  "                               with different call stack\n"
  "--no-summary-optimization      do not attempt to remove superfluous\n"
  "                               summaries (saves few cheap SAT calls)\n"
  "--no-itp                       do not construct summaries (just report SAFE/BUG)\n"

#ifdef USE_PERIPLO
  "\nPeRIPLO options (only if compiled):\n"
  //  "--reduce-proof-time <fraction> use up to <fraction> of SAT solving time\n"
  //  "                               to reduce proof --> smaller summaries\n"
  "--reduce-proof-graph <int>     use <int> graph traversals for each global loop\n"
  "                                               --> smaller summaries\n"
  "--reduce-proof-loops <int>     use <int> global reduction loops\n"
  "                                               --> smaller summaries\n"
  "--tree-interpolants            produce tree interpolants\n"
  "--color-proof <mode>:          try different coloring strategies:\n"
  "  0                            random\n"
  "  1                            from external file \"__common\"\n"
  "  2                            TBD\n"
  "--itp-algorithm <mode>:        set up interpolating algorithm:\n"
  "  0                            Pudlak\n"
  "  1                            McMillan\n"
  "  2                            McMillanPrime\n"
  "--proof-trans <mode>:          transform proof:\n"
  "  1                            to make stronger interpolants\n"
  "  2                            to make weaker interpolants\n"
  "--check-itp                    check interpolants with Z3\n"
  "--verbose-solver <number>      set SAT solver verbosity (if applicable)\n"
#else
  "\nOpenSMT options :\n"
  "--random-seed <number>         set up random seed to manipulate proof size\n"
  "--verbose-solver <number>      set SAT solver verbosity (if applicable)\n"
#endif

  "\nRefinement options:\n"
  "--refine-mode <mode>:\n"
  "  0 | \"force-inlining\"         inline every function call\n"
  "                               after an unsuccessful attempt\n"
  "                               of summary substitution\n"
  "  1 | \"random-substitution\"    try to randomly choose function calls\n"
  "                               to be inlined\n"
  "  2 | \"slicing-result\"         try to choose function calls to be inlined\n"
  "                               based on slicing results\n"
  "\nOptions of first refinement iteration:\n"
  "--init-mode <mode>\n"
  "  0 | \"havoc-all\"              start with nondeterministic assignments\n"
  "                               for all function calls\n"
  "  1 | \"use-summaries\"          start with substituting all existent summaries\n"
  "                               for all function calls\n"
//  "                               is being disabled by \"force-inlining\"\n"
  "\nI/O options:\n"
  "--xml-ui                       use XML-formatted output\n"
  "--xml-interface                stdio-XML interface\n"
  "\n";
}

/*******************************************************************\
  
 Function: 

 Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

unsigned funfrog_parseoptionst::count(const goto_functionst &goto_functions) const
{
  unsigned long c=0;
  for(goto_functionst::function_mapt::const_iterator it =
        goto_functions.function_map.begin();
      it!=goto_functions.function_map.end();
      it++)
    c += it->second.body.instructions.size();
  std::cout << "    Instruction count: " << c << std::endl;
  return c;
}

/*******************************************************************\
  
 Function: 

 Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

unsigned funfrog_parseoptionst::count(const goto_programt &goto_program) const
{
  std::cout << "    Instruction count: " << goto_program.instructions.size()
    << std::endl;
  return goto_program.instructions.size();
}


bool funfrog_parseoptionst::check_function_summarization(
  namespacet &ns,
  goto_functionst &goto_functions)
{

  fine_timet before, after;
  
  claim_mapt claim_map;
  claim_numberst claim_numbers;

  
  status("Checking claims in program...");

  unsigned claim_nr=0;

  get_claims(goto_functions, claim_map, claim_numbers);

  if(cmdline.isset("show-claims"))
  {
    show_claims(ns, claim_map, claim_numbers, get_ui());
    return 0;
  }

  bool init_upg_check = cmdline.isset("init-upgrade-check");
  bool upg_check = cmdline.isset("do-upgrade-check");

  if (upg_check || init_upg_check){
    // perform the upgrade check (or preparation to it)
    if(cmdline.isset("testclaim") || cmdline.isset("claim") ||
        cmdline.isset("claimset") || cmdline.isset("no-itp"))
    {
      error("Upgrade checking mode does not allow checking specific claims and needs interpolation");
      return 1;
    }

    bool init_ready = true; // the checks of existence of __omega and upg. version will be later
    if (init_upg_check){
      init_ready = check_initial(ns, goto_functions.function_map[ID_main].body,
              goto_functions, options, ui_message_handler, !cmdline.isset("no-progress"));
    }

    if (upg_check && init_ready){
      goto_functionst goto_functions_new;
      status(std::string("Loading an upgrade: `")+cmdline.getval("do-upgrade-check")+"' ...");
      before=current_time();

      if(get_goto_program(cmdline.getval("do-upgrade-check"), ns, options, goto_functions_new))
        return 6;

      after=current_time();
      status() << "    LOAD Time: " << (after-before) << " sec." << eom;
      check_upgrade(ns,
              // OLD!
              goto_functions.function_map[ID_main].body, goto_functions,
              // NEW!
              goto_functions_new.function_map[ID_main].body, goto_functions_new,
              options, ui_message_handler, !cmdline.isset("no-progress"));
    }
  } else {
    // perform standalone check (all the functionality remains the same)
  
    if(cmdline.isset("claim") &&
        (cmdline.isset("all-claims") || cmdline.isset("claimset") || cmdline.isset("claims-order"))) {
      error("A specific claim cannot be specified if any other claim specification is set.");
      return 1;
    }

    if(cmdline.isset("all-claims") &&
        (cmdline.isset("claimset") || cmdline.isset("claims-order"))) {
      error("All claims cannot be specified if any other claim specification is set.");
      return 1;
    }

    if(cmdline.isset("claimset") && cmdline.isset("claims-order")) {
      error("A specific claimset cannot be specified if any other claim specification is set.");
      return 1;
    }
    else if(cmdline.isset("claim")) {
      claim_nr=atoi(cmdline.getval("claim"));
      if (claim_nr == 0 || claim_nr > claim_numbers.size()) {
        error("Testclaim not found.");
        return 1;
      }
    }

    before=current_time();
    claim_statst stats = check_claims(ns,
                                      goto_functions.function_map[ID_main].body,
                                      goto_functions,
                                      claim_map,
                                      claim_numbers,
                                      options,
                                      ui_message_handler,
                                      claim_nr);
    after=current_time();
  }

  return 0;
}

/*******************************************************************\
  
 Function: 

 Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void funfrog_parseoptionst::set_options(const cmdlinet &cmdline)
{
  options.set_option("bounds-check", cmdline.isset("bounds-check"));
  options.set_option("pointer-check", cmdline.isset("pointer-check"));
  options.set_option("div-by-zero-check", cmdline.isset("div-by-zero-check"));
  options.set_option("signed-overflow-check", cmdline.isset("overflow-check"));
  options.set_option("unsigned-overflow-check", cmdline.isset("overflow-check"));
  options.set_option("nan-check", cmdline.isset("nan-check"));
  options.set_option("string-abstraction", cmdline.isset("string-abstraction"));
  options.set_option("assertions", cmdline.isset("assertions"));
  options.set_option("all-claims", cmdline.isset("all-claims"));
  options.set_option("save-queries", cmdline.isset("save-queries"));
  options.set_option("no-slicing", cmdline.isset("no-slicing"));
  options.set_option("no-itp", cmdline.isset("no-itp"));
  options.set_option("no-assert-grouping", cmdline.isset("no-assert-grouping"));
  options.set_option("no-summary-optimization", cmdline.isset("no-summary-optimization"));
  options.set_option("tree-interpolants", cmdline.isset("tree-interpolants"));
  options.set_option("init-upgrade-check", cmdline.isset("init-upgrade-check"));
  options.set_option("check-itp", cmdline.isset("check-itp"));

  // always check assertions
  options.set_option("assertions", true);

  // always use assumptions
  options.set_option("assumptions", true);

  if (cmdline.isset("itp-algorithm")) {
    options.set_option("itp-algorithm", cmdline.getval("itp-algorithm"));
  }

  if (cmdline.isset("proof-trans")) {
    options.set_option("proof-trans", cmdline.getval("proof-trans"));
  }

  if (cmdline.isset("unwind")) {
    options.set_option("unwind", cmdline.getval("unwind"));
  }
  if (cmdline.isset("unwindset")) {
    options.set_option("unwindset", cmdline.getval("unwindset"));
  }
  if (cmdline.isset("claimset")) {
    options.set_option("claimset", cmdline.getval("claimset"));
  }
  if (cmdline.isset("claims-order")) {
    options.set_option("claims-order", cmdline.getval("claims-order"));
  }
  if (cmdline.isset("do-upgrade-check")) {
    options.set_option("do-upgrade-check", cmdline.getval("do-upgrade-check"));
  }
  if (cmdline.isset("save-summaries")) {
    options.set_option("save-summaries", cmdline.getval("save-summaries"));
  } else {
    options.set_option("save-summaries", "__summaries");
  }
  if (cmdline.isset("save-omega")) {
    options.set_option("save-omega", cmdline.getval("save-omega"));
  } else {
    options.set_option("save-omega", "__omega");
  }
  if (cmdline.isset("load-summaries")) {
    options.set_option("load-summaries", cmdline.getval("load-summaries"));
  } else {
    options.set_option("load-summaries", "__summaries");
  }
  if (cmdline.isset("load-omega")) {
    options.set_option("load-omega", cmdline.getval("load-omega"));
  } else {
    options.set_option("load-omega", "__omega");
  }
  if (cmdline.isset("save-change-impact")) {
    options.set_option("save-change-impact", cmdline.getval("save-change-impact"));
  } else {
    options.set_option("save-change-impact", "__calltree.xml");
  }
  if (cmdline.isset("reduce-proof-time")) {
    options.set_option("reduce-proof-time", cmdline.getval("reduce-proof-time"));
  }
  if (cmdline.isset("reduce-proof-graph")) {
    options.set_option("reduce-proof-graph", cmdline.getval("reduce-proof-graph"));
  }
  if (cmdline.isset("reduce-proof-loops")) {
    options.set_option("reduce-proof-loops", cmdline.getval("reduce-proof-loops"));
  }
  if (cmdline.isset("random-seed")) {
    options.set_option("random-seed", cmdline.getval("random-seed"));
  }
  if (cmdline.isset("color-proof")) {
    options.set_option("color-proof", cmdline.getval("color-proof"));
  } else {
    options.set_option("color-proof", "-1");
  }
  if (cmdline.isset("verbose-solver")) {
    options.set_option("verbose-solver", cmdline.getval("verbose-solver"));
  }
  if (cmdline.isset("refine-mode")) {
    options.set_option("refine-mode", cmdline.getval("refine-mode"));
  }
  if (cmdline.isset("init-mode")) {
    options.set_option("init-mode", cmdline.getval("init-mode"));
  }
}
