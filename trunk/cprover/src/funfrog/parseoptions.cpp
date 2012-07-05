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

//#include <message.h>
#include <context.h>
#include <i2string.h>
#include <std_expr.h>
#include <arith_tools.h>
#include <prefix.h>
#include <time_stopping.h>

#include <goto-programs/read_goto_binary.h>
#include <goto-programs/goto_functions.h>
#include <goto-programs/goto_function_pointers.h>
#include <goto-programs/goto_convert_functions.h>
#include <goto-programs/goto_inline.h>
#include <goto-programs/goto_check.h>
#include <goto-programs/string_instrumentation.h>
#include <goto-programs/string_abstraction.h>
#include <goto-programs/slicer.h>
//#include <goto-programs/show_claims.h>
#include <goto-programs/remove_unused_functions.h>
#include <goto-programs/link_to_library.h>

#include <pointer-analysis/add_failed_symbols.h>
#include <pointer-analysis/value_set_analysis.h>
#include <pointer-analysis/value_set_analysis_fi.h>
#include <pointer-analysis/value_set_analysis_fivr.h>
#include <pointer-analysis/value_set_analysis_fivrns.h>
#include <pointer-analysis/goto_program_dereference.h>

#include "version.h"
#include "parseoptions.h"
#include "../loopfrog/version.h"
#include "../loopfrog/value_set_alloc_adaptor.h"
#include "../loopfrog/memstat.h"
#include "../loopfrog/replace_malloc.h"
#include "../loopfrog/program_compression.h"
#include "check_claims.h"
#include "upgrade_checker.h"
#include "inlined_claims.h"
#include "../loopfrog/languages.h"

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
        context, get_message_handler(), goto_functions);

    status("Function Pointer Removal");
    remove_function_pointers(ns, goto_functions);

    status("Partial Inlining");
    // do partial inlining
    goto_partial_inline(goto_functions, ns, ui_message_handler);

    status("Generic Property Instrumentation");
    // add generic checks
    goto_check(ns, options, goto_functions);

    if(cmdline.isset("string-abstraction"))
    {
      status("String Abstraction");
      string_abstraction(context,
        get_message_handler(), goto_functions);
    }

    // add failed symbols
    // needs to be done before pointer analysis
    add_failed_symbols(context);

    if(cmdline.isset("pointer-check"))
    {
      status("Pointer Analysis");
      value_set_analysist value_set_analysis(ns);
      value_set_analysis(goto_functions);


      status("Adding Pointer Checks");

      // add pointer checks
      pointer_checks(
        goto_functions, ns, options, value_set_analysis);
    }

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
           context, goto_functions, get_message_handler()))
        return true;

      config.ansi_c.set_from_context(context);

      if(context.symbols.find(ID_main)==context.symbols.end())
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

      if(context.symbols.find(ID_main)==context.symbols.end())
      {
        error("No entry point; please provide a main function");
        return true;
      }

      status("Generating GOTO Program");

      goto_convert(
        context, options, goto_functions,
        ui_message_handler);

      // finally add the library
      status("Adding CPROVER library");
      link_to_library(
        context, goto_functions, options, ui_message_handler);
    }

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

  std::string stats_dir;
  if(cmdline.isset("save-stats") ||
     cmdline.isset("save-claims") ||
     cmdline.isset("save-loops"))
  {
    stats_dir = cmdline.args[0] + "_data/";
    #ifndef _WIN32
      mkdir(stats_dir.c_str(), S_IRWXU | S_IRGRP | S_IROTH);
    #else
      mkdir(stats_dir.c_str());
    #endif
  }

  if(cmdline.isset("save-stats"))
  {
    std::string fn=cmdline.args[0]+".lfstat";
    statfile.open(fn.c_str(), std::ios_base::app);
    statfile << cmdline.args[0] << ";";
    statfile.flush();
  }

  if(cmdline.isset("save-summaries"))
  {
    // clean those files
    std::ofstream f("summaries_imprecise"); f.close();
    std::ofstream g("summaries_precise"); g.close();
  }

  register_languages();

  goto_functionst goto_functions;
  namespacet ns(context);
  fine_timet before, after;

  status(std::string("Loading `")+cmdline.args[0]+"' ...");
  before=current_time();
  
  if(get_goto_program(cmdline.args[0], ns, options, goto_functions))
    return 6;

  after=current_time();
  status(std::string("    LOAD Time: ") + time2string(after-before) + " sec.");

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

  if(check_function_summarization(ns, goto_functions, stats_dir))
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
  "--bounds-check                 add array bounds checks\n"
  "--pointer-check                add pointer checks\n"
  "--assertions                   add user supplied assertions\n"
  "--claim <int>                  check a specific claim\n"
  "--testclaim <label>            check a labelled claim\n"
  "--unwind <bound>               loop unwind bound\n"
  "--unwindset <label:bound,...>  set of loop unwind bound for specific\n"
  "                               loops\n"
  "--no-slicing                   no slicing of the SSA program form (slower\n"
  "                               computation, more dependable result)\n"
  "--no-assert-grouping           do not group checks for the same assertion\n"
  "                               with different call stack\n"
  "--no-summary-optimization      do not attempt to remove superfluous\n"
  "                               summaries (saves few cheap SAT calls)\n"
  "--reduce-proof <fraction>      use up to <fraction> of SAT solving time\n"
  "                               to reduce proof --> smaller summaries\n"
  "--verbose-solver <number>      set SAT solver verbosity (if applicable)\n"

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
  "--steps <bound>                number of refinement steps\n"
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

/*******************************************************************\
  
 Function: 

 Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

unsigned long funfrog_parseoptionst::report_mem(void) const
{
  unsigned long l = current_memory();
  unsigned long mbs = l / 1048576;

  std::cout << "    MEM: "
  << mbs << " MB " <<
  "(" << l << " Bytes)." << std::endl;

  return mbs;
}

/*******************************************************************\
  
 Function: 

 Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

unsigned long funfrog_parseoptionst::report_max_mem(unsigned long mem) const
{
  unsigned long mbs = mem / 1048576;

  std::cout << "    MEM: "
  << mbs << " MB " <<
  "(" << mem << " Bytes)." << std::endl;

  return mbs;
}


/*******************************************************************\
  
 Function: 

 Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

bool funfrog_parseoptionst::check_function_summarization(
  namespacet &ns,
  goto_functionst &goto_functions,
  std::string &stats_dir)
{
  //unsigned long mem;
  //unsigned inst;
  fine_timet before, after;
  
  claim_mapt claim_map;
  claim_numberst claim_numbers;
  /*  
  // we don't create copies...
  goto_functionst &leaping_functions = goto_functions;
  
  loop_summarizer_statst sumstats;
  
  // Stage 10: The loop summarization
  status("#10: Loop Summarization...");
  
  loopstoret imprecise_loops;
  loopstoret precise_loops;


  string_summarizationt strsum( context, leaping_functions, imprecise_loops, precise_loops,adaptor, stats_dir, options );

  before=current_time();
  sumstats = summarize(goto_functions, context, strsum,
                       imprecise_loops, precise_loops, adaptor,
                       get_message_handler(), cmdline, stats_dir);
  if(!cmdline.isset("no-progress") &&
     !cmdline.isset("no-invariants"))
    strsum.print_statistics(std::cout);
  after=current_time();
  status(std::string("    LS Time: ") + time2string(after-before) + " sec.");
  if(cmdline.isset("no-invariants"))
    mem = report_mem();
  else
    mem=report_max_mem(strsum.max_mem_used);
  inst=count(goto_functions, imprecise_loops, precise_loops, 0);
  
  if(cmdline.isset("save-stats"))
  {
    statfile << "LS;" << time2string(after-before) << ";" << mem << ";" <<
      inst << ";" << strsum.seen_loops << ";" << sumstats.good << ";" <<
      sumstats.bad << ";";
    statfile.flush();
  }
  
  Forall_goto_functions(it, leaping_functions)
  {
    compress_program(it->second.body);
    it->second.body.update();
  }
  
  if (cmdline.isset("show-leaping-program"))
  {
    forall_goto_functions(it, leaping_functions)
    {
      std::cout << it->first << ": " << std::endl;
      std::cout << "---------------" << std::endl;
      it->second.body.output(ns, "", std::cout);
    }
  
    return true;
  }
  
  if (cmdline.isset("save-leaping-program"))
  {
    std::ofstream f((stats_dir+"goto_program_leaping").c_str());
    forall_goto_functions(it, leaping_functions)
    {
      f << it->first << ": " << std::endl;
      f << "---------------" << std::endl;
      it->second.body.output(ns, "", f);
    }
    f.close();
  }
  */
  
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
    if(cmdline.isset("testclaim") || cmdline.isset("claim"))
    {
      error("Upgrade checking mode does not allow checking specific claims.");
      return 1;
    }

    bool init_ready = true; // the checks of existence of __omega and upg. version will be later
    if (init_upg_check){
      init_ready = check_initial(ns, goto_functions.function_map[ID_main].body,
              goto_functions, options, ui_message_handler, !cmdline.isset("no-progress"));
    }

    if (upg_check && init_ready){
      goto_functionst goto_functions_new;
      status(std::string("Loading `")+cmdline.getval("do-upgrade-check")+"' ...");
      before=current_time();

      if(get_goto_program(cmdline.getval("do-upgrade-check"), ns, options, goto_functions_new))
        return 6;

      after=current_time();
      status(std::string("    LOAD Time: ") + time2string(after-before) + " sec.");

      check_upgrade(ns,
              // OLD!
              goto_functions.function_map[ID_main].body, goto_functions,
              // NEW!
              goto_functions_new.function_map[ID_main].body, goto_functions_new,
              options, ui_message_handler, !cmdline.isset("no-progress"));
    }
  } else {
    // perform standalone check (all the functionality remains the same)
  
    if(cmdline.isset("testclaim"))
    {
      claim_nr=find_marked_claim(goto_functions,
                                 cmdline.getval("testclaim"),
                                 claim_numbers);
      if(claim_nr==(unsigned) -1)
      {
        claim_nr = atoi(cmdline.getval("testclaim"));
        if (claim_nr == 0 || claim_nr > claim_numbers.size()) {
          error("Testclaim not found.");
          return 1;
        }
      }
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
                                      stats_dir,
                                      claim_map,
                                      claim_numbers,
                                      options,
                                      ui_message_handler,
                                      claim_nr,
                                      cmdline.isset("show-pass"),
                                      !cmdline.isset("suppress-fail"),
                                      !cmdline.isset("no-progress"),
                                      cmdline.isset("save-claims"));
    after=current_time();
  }
  /*
  if(!cmdline.isset("no-progress")) std::cout << "\r";
  status(std::string("    PASS: ")+i2string(stats.claims_passed +
                                            sumstats.good)+
                        " FAIL: "+i2string(stats.claims_failed) + " ");
  status(std::string("    CC Time: ") + time2string(after-before) + " sec.");
  status(std::string("    Time spent in SAT SOLVER: ") +
           time2string(global_satsolver_time) + " sec.");
  status(std::string("    Time spent in SAT CONVERSION: ") +
             time2string(global_sat_conversion_time) + " sec.");
  mem=report_max_mem(stats.max_mem_used);
  inst=count(goto_functions, imprecise_loops,
             precise_loops, stats.max_instruction_count);
  
  if(cmdline.isset("save-stats"))
  {
    statfile << "CC;" << time2string(after-before) << ";" << mem << ";" <<
      inst << ";CLAIMS;" << stats.claims_passed << ";" <<
      stats.claims_failed <<
      ";SAT;" << time2string(global_satsolver_time) <<
      ";SCONV;" << time2string(global_sat_conversion_time) << ";";
    statfile.close();
  }
  */

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
  options.set_option("string-abstraction", cmdline.isset("string-abstraction"));
  options.set_option("assertions", cmdline.isset("assertions"));
  options.set_option("save-queries", cmdline.isset("save-queries"));
  options.set_option("no-slicing", cmdline.isset("no-slicing"));
  options.set_option("no-assert-grouping", cmdline.isset("no-assert-grouping"));
  options.set_option("no-summary-optimization", cmdline.isset("no-summary-optimization"));
  options.set_option("init-upgrade-check", cmdline.isset("init-upgrade-check"));
  
  if (cmdline.isset("unwind")) {
    options.set_option("unwind", cmdline.getval("unwind"));
  }
  if (cmdline.isset("unwindset")) {
    options.set_option("unwindset", cmdline.getval("unwindset"));
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
  if (cmdline.isset("reduce-proof")) {
    options.set_option("reduce-proof", cmdline.getval("reduce-proof"));
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
  if (cmdline.isset("steps")) {
    options.set_option("steps", cmdline.getval("steps"));
  } else {
    options.set_option("steps", "5");
  }
}
