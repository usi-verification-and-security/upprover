/*******************************************************************\

 Module: Command Line Parsing

 Author: Daniel Kroening, kroening@kroening.com
         CM Wintersteiger
         Ondrej Sery

\*******************************************************************/

#include <config.h>
#include <iostream>
#include <sys/time.h>
#include <sys/stat.h>
#ifndef _WIN32
#include <sys/resource.h>
#else
#include <io.h>
#endif

#include <std_expr.h>
#include <arith_tools.h>
#include <prefix.h>
#include <time_stopping.h>

#include <goto-programs/goto_convert_functions.h>
#include <goto-programs/remove_function_pointers.h>
#include <goto-programs/remove_asm.h>
#include <goto-programs/remove_virtual_functions.h>
#include <goto-programs/remove_exceptions.h>
#include <goto-programs/remove_instanceof.h>
#include <goto-programs/remove_returns.h>
#include <goto-programs/remove_vector.h>
#include <goto-programs/remove_complex.h>
#include <goto-symex/rewrite_union.h>
#include <goto-symex/adjust_float_expressions.h>
#include <goto-programs/goto_inline.h>
#include <goto-programs/show_properties.h>
#include <goto-programs/set_properties.h>
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
#include "version.h"
#include "parseoptions.h"


/*******************************************************************

 Function: funfrog_parseoptionst::funfrog_parseoptionst

 Inputs:

 Outputs:

 Purpose: constructor

 \*******************************************************************/

funfrog_parseoptionst::funfrog_parseoptionst(int argc, const char **argv):
  parse_options_baset(FUNFROG_OPTIONS, argc, argv),
  xml_interfacet(cmdline),
  //language_uit((std::string("FUNFROG") + FUNFROG_VERSION), cmdline)      
  //language_uit(cmdline, *(new ui_message_handlert(ui_message_handlert::PLAIN, "FUNFROG" FUNFROG_VERSION)))
  language_uit(cmdline, *(new ui_message_handlert(cmdline, "FUNFROG " FUNFROG_VERSION)))
{
}

bool funfrog_parseoptionst::process_goto_program(
  namespacet& ns,
  optionst& options,
  goto_functionst &goto_functions)
{
  try
  {
    // KE: update  new cprover version - taken from: cbmc_parseoptionst::process_goto_program
    // Consider adding more optimizations as full slicing or non-det statics
      
    // Remove inline assembler; this needs to happen before
    // adding the library.
    remove_asm(symbol_table, goto_functions);

    // add the library
    link_to_library(symbol_table, goto_functions, ui_message_handler);  
      
    if(cmdline.isset("string-abstraction"))
      string_instrumentation(
        symbol_table, get_message_handler(), goto_functions);

    status() << "Removal of function pointers and virtual functions" << eom;
    remove_function_pointers(
      get_message_handler(),
      symbol_table,
      goto_functions,
      cmdline.isset("pointer-check"));
    // Java virtual functions -> explicit dispatch tables:
    remove_virtual_functions(symbol_table, goto_functions);
    // remove catch and throw
    remove_exceptions(symbol_table, goto_functions);
    // Similar removal of RTTI inspection:
    remove_instanceof(symbol_table, goto_functions);

    // do partial inlining
    status() << "Partial Inlining" << eom;
    goto_partial_inline(goto_functions, ns, ui_message_handler);

    // remove returns, gcc vectors, complex
    // remove_returns(symbol_table, goto_functions); //KE: causes issues with theoref
    remove_vector(symbol_table, goto_functions);
    remove_complex(symbol_table, goto_functions);
    rewrite_union(goto_functions, ns);

    // add generic checks
    status() << "Generic Property Instrumentation" << eom;
    goto_check(ns, options, goto_functions);

    // checks don't know about adjusted float expressions
    adjust_float_expressions(goto_functions, ns);
    
    if(cmdline.isset("string-abstraction"))
    {
      status() << "String Abstraction" << eom;
      string_abstraction(
        symbol_table,
        get_message_handler(),
        goto_functions);
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
    cbmc_error_interface(e);
    return true;
  }

  catch(const std::string e)
  {
    cbmc_error_interface(e);
    return true;
  }

  catch(int)
  {
    return true;
  }

  catch(std::bad_alloc)
  {
    cbmc_error_interface("Out of memory");
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
    cbmc_error_interface("Please provide a program to verify");
    return true;
  }

  try
  {
    if(cmdline.args.size()==1 &&
       is_goto_binary(filename))
    {
      cbmc_status_interface("Reading GOTO program from file");

      if(read_goto_binary(filename,
           symbol_table, goto_functions, get_message_handler()))
        return true;

      config.set_from_symbol_table(symbol_table);

      if(symbol_table.symbols.find(goto_functionst::entry_point())==symbol_table.symbols.end())
      {
        cbmc_error_interface("The goto binary has no entry point; please complete linking");
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

      if(symbol_table.symbols.find(goto_functionst::entry_point())==symbol_table.symbols.end())
      {
        cbmc_error_interface("No entry point; please provide a main function");
        return true;
      }

      cbmc_status_interface("Generating GOTO Program");

      goto_convert(symbol_table, goto_functions, ui_message_handler);

    }

    // finally add the library
    cbmc_status_interface("Adding CPROVER library");
    link_to_library(symbol_table, goto_functions, ui_message_handler);

    if(process_goto_program(ns, options, goto_functions))
      return true;
  }

  catch(const char *e)
  {
    cbmc_error_interface(e);
    return true;
  }

  catch(const std::string e)
  {
    cbmc_error_interface(e);
    return true;
  }

  catch(int)
  {
    return true;
  }

  catch(std::bad_alloc)
  {
    cbmc_error_interface("Out of memory");
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
    verbosity=atoi(cmdline.get_value("v").c_str());
    //set_verbosity(verbosity);
    ui_message_handler.set_verbosity(verbosity);
  }

  if(cmdline.args.size()==0)
  {
    cbmc_error_interface("Please provide an input file.");
    return 1;
  }
  else if (cmdline.args.size()>1)
  {
    cbmc_error_interface("Multiple input files not supported.");
    return 1;
  }

  std::ifstream infile(cmdline.args[0].c_str());
  if (!infile)
  {
    cbmc_error_interface(std::string("Error opening file `")+cmdline.args[0]+"'.");
    return 1;
  }

  goto_functionst goto_functions;
  namespacet ns(symbol_table);
  absolute_timet before, after;

  cbmc_status_interface(std::string("Loading `")+cmdline.args[0]+"' ...");
  before=current_time();
  
  if(get_goto_program(cmdline.args[0], ns, options, goto_functions))
    return 6;

  after=current_time();
  cbmc_status_interface(std::string("    LOAD Time: ") + (after-before).as_string() + std::string(" sec."));


  label_properties(goto_functions);

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
//    cbmc_status_interface("Please set either ratio or time for reduction or number of proof traversals.");
//    return false;
//  }

  if(check_function_summarization(ns, goto_functions))
    return 1;

  cbmc_status_interface("#X: Done.");

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
    "* * *                HiFrog " << HIFROG_VERSION
//    " - Copyright (C) 2016                    * * *\n"
//    "          Ondrej Sery, Grigory Fedyukovich & Natasha Sharygina\n\n"
//    "                based on FUNFROG " << FUNFROG_VERSION
//    " - Copyright (C) 2013               * * *\n"
//    "                based on eVolCheck " << EVOLCHECK_VERSION
//    " - Copyright (C) 2013             * * *\n"
//    "          Ondrej Sery, Grigory Fedyukovich & Natasha Sharygina\n\n"
  "\n"
  "Usage:                         Purpose:\n"
  "\n"
  " hifrog [-?] [-h] [--help]     show help\n"
  " hifrog [options] <file>       run on goto-binary `file'\n"
  "\nGeneral Purpose options:\n"
  "--version                      show version information\n"
  "--save-summaries <filename>    save collected function summaries\n"
  "                               to the given file\n"
  "--load-summaries <filename>    load function summaries\n"
  "                               from the given file\n"
  "--show-claims                  output the claims list\n"
  "--claims-count                 output the total number of claims\n"
//  "--bounds-check                 enable array bounds checks\n"
//  "--div-by-zero-check            enable division by zero checks\n"
//  "--pointer-check                enable pointer checks\n"
//  "--overflow-check               enable arithmetic over- and underflow checks\n"
//  "--nan-check                    check floating-point for NaN\n"
  "--claim <int>                  check a specific claim\n"
  "--all-claims                   check all claims in one run\n"
  "--claims-opt <steps>           remove weaker claims using the given treshold\n"
  "                               (treshold = number of SSA steps)\n"
  "                               and check stronger claims at once\n"
  "--unwind <bound>               loop unwind bound\n"
  "--type-constraints             LRA's basic constraints on numerical data type\n"
  "                                 0 for no additional constraints,\n"
  "                                 1 for type constraints on non-deterministic input\n"
  "                                 2 for type constraints on variables\n"
  "--no-slicing                   no slicing of the SSA program form (slower\n"
  "                               computation, more dependable result)\n"
  "--no-assert-grouping           do not group checks for the same assertion\n"
  "                               with different call stack\n"
  "--no-summary-optimization      do not attempt to remove superfluous\n"
  "                               summaries (saves few cheap SAT calls)\n"
  "--no-error-trace               disable the counter example's print once a real bug found\n"
#ifdef PRODUCE_PROOF          
  "--no-itp                       do not construct summaries (just report SAFE/BUG)\n"
#endif
  "--no-partitions                do not use partitions to create the bmc formula\n\n"        
  "\nSMT, Interpolation and Proof Reduction options:\n"
  "--theoref                      use experimental Theory Refining algorithm\n"
  "--force                        force refining CUF to BV without counterexamples\n"
  "--custom <n1,n2,..>            program statement ids to be refined (without counterexamples)\n"
  "--heuristic <n>                refinement schema:\n"
  "                                 0 - forward\n"
  "                                 1 - backward\n"
  "                                 2 - forward with multiple refinement\n"
  "                                 3 - backward with multiple refinement\n"
  "                                 4 - forward with dependencies\n"
  "                                 5 - backward with dependencies\n"
  "                                 6 - forward with multiple refinement & dependencies\n"
  "                                 7 - backward with multiple refinement & dependencies\n"
  "--bitwidth <n>                 bitwidth for the CUF BV mode\n\n"
  "--logic <logic>                [qfuf, qfcuf, qflra, prop] if not present qfuf is used\n"
#ifdef PRODUCE_PROOF           
  "--itp-algorithm                propositional interpolation algorithm: \n"
  "                                 0 for McMillan_s,\n"
  "                                 1 for Pudlak,\n"
  "                                 2 for McMillan_w\n"
  "--itp-uf-algorithm             EUF interpolation algorithm:\n"
  "                                 0 for Strong,\n"
  "                                 2 for Weak,\n"
  "                                 3 for Random\n"
  "--itp-lra-algorithm            LRA interpolation algorithm:\n"
  "                                 0 for Strong,\n"
  "                                 2 for Weak\n"
  "                                 3 for custom factor.\n"
  "--itp-lra-factor               LRA interpolation strength factor:\n"
  "                               must be a fraction in the interval [0,1)\n"
  "--reduce-proof                 enable Proof Reduction\n"
  "--reduce-proof-graph           number of graph traversals per reduction iteration\n"
  "--reduce-proof-loops           number of reduction iterations\n"
#endif          
  "--list-templates               dump the templates of the functions for user-defined summaries\n"
  "--dump-query                   ask OpenSMT to dump the smtlib query before solving\n"
  "--dump-query-name <base>       base name for the files where queries are dumped\n"
//  "\nRefinement options:\n"
//  "--refine-mode <mode>:\n"
//  "  0 | \"force-inlining\"         inline every function call\n"
//  "                               after an unsuccessful attempt\n"
//  "                               of summary substitution\n"
//  "  1 | \"random-substitution\"    try to randomly choose function calls\n"
//  "                               to be inlined\n"
//  "  2 | \"slicing-result\"         try to choose function calls to be inlined\n"
//  "                               based on slicing results\n"
//  "\nOptions of first refinement iteration:\n"
//  "--init-mode <mode>\n"
//  "  0 | \"havoc-all\"              start with nondeterministic assignments\n"
//  "                               for all function calls\n"
//  "  1 | \"use-summaries\"          start with substituting all existent summaries\n"
//  "                               for all function calls\n"
//  "                               is being disabled by \"force-inlining\"\n"
//  "\nI/O options:\n"
//  "--xml-ui                       use XML-formatted output\n"
//  "--xml-interface                stdio-XML interface\n"
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

    claim_mapt claim_map;
    claim_numberst claim_numbers;
    unsigned claim_nr=0;

    get_claims(goto_functions, claim_map, claim_numbers);
    cbmc_status_interface("Checking claims in program...(" + std::to_string(claim_numbers.size())+")");

    if(cmdline.isset("show-claims")|| // will go away
	 cmdline.isset("show-properties")) // use this one
    {
	  const namespacet ns(symbol_table);
	  show_properties(ns, get_ui(), goto_functions);
	  return 0;
    } else if(cmdline.isset("claims-count")) {
        std::cout <<"(claims-count),"<< claim_numbers.size() << std::endl;
        return 0;
    }

    // perform standalone check (all the functionality remains the same)
  
    if(cmdline.isset("claim") &&
        (cmdline.isset("all-claims") || cmdline.isset("claimset") || cmdline.isset("claims-order"))) {
      cbmc_error_interface("A specific claim cannot be specified if any other claim specification is set.");
      return 1;
    }

    if(cmdline.isset("all-claims") &&
        (cmdline.isset("claimset") || cmdline.isset("claims-order"))) {
      cbmc_error_interface("All claims cannot be specified if any other claim specification is set.");
      return 1;
    }

    if(cmdline.isset("claimset") && cmdline.isset("claims-order")) {
      cbmc_error_interface("A specific claimset cannot be specified if any other claim specification is set.");
      return 1;
    }
    else if(cmdline.isset("claim")) {
      claim_nr=atoi(cmdline.get_value("claim").c_str());
      if (claim_nr == 0 || claim_nr > claim_numbers.size()) {
    	cbmc_error_interface("Testclaim not found.");
        return 1;
      }
    } 
    
    if (cmdline.isset("claims-opt"))
      store_claims(ns, claim_map, claim_numbers);
    
    // If we set bitwidth, check it sets right, it will be by defualt 8
    if (options.get_option("logic") == "qfcuf") // bitwidth exists only in cuf
    {
        unsigned bitwidth = options.get_unsigned_int_option("bitwidth");  
        if (!((bitwidth != 0) && !(bitwidth & (bitwidth - 1)))) {
            cbmc_error_interface("Error: invalid --bitwidth " + cmdline.get_value("bitwidth")
                + ". Please re-run with bit-width parameter that is a pow of 2!");
            exit(0);
        } else if (bitwidth > 32) {
            cbmc_status_interface("Warrning: --bitwidth larger than 32-bits has only partial support in qfcuf");   
        }  
    }

    // ID_main is the entry point that is now changed to be ID__start
    // KE: or is it goto_functionst::entry_point()?
    // So instead of c::main we have now _start (cbmc 5.5)
    check_claims(ns,
                                      goto_functions.function_map[goto_functionst::entry_point()].body,
                                      goto_functions,
                                      claim_map,
                                      claim_numbers,
                                      options,
                                      ui_message_handler,
                                      claim_nr);
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
  options.set_option("all-claims", cmdline.isset("all-claims"));
  options.set_option("save-queries", cmdline.isset("save-queries"));
  options.set_option("no-slicing", cmdline.isset("no-slicing"));
#ifdef PRODUCE_PROOF   
  options.set_option("no-itp", cmdline.isset("no-itp"));
  status() << "\n*** USING INTERPOLATION AND SUMMARIES (DPRODUCE_PROOF is on) ***\n" << eom;
#else
  options.set_option("no-itp", true); // If not using itp, this flag is true always!
  status() << "\n*** NO ITERPOLATION MODE, NOT USING SUMMARY FILES (DPRODUCE_PROOF is off) ***\n" << eom;
#endif  
  options.set_option("no-partitions", cmdline.isset("no-partitions"));
  options.set_option("no-assert-grouping", cmdline.isset("no-assert-grouping"));
  options.set_option("no-summary-optimization", cmdline.isset("no-summary-optimization"));
  options.set_option("tree-interpolants", cmdline.isset("tree-interpolants"));
  options.set_option("check-itp", cmdline.isset("check-itp"));
  options.set_option("no-error-trace", cmdline.isset("no-error-trace"));
  options.set_option("list-templates", cmdline.isset("list-templates"));
  options.set_option("reduce-proof", cmdline.isset("reduce-proof"));
  options.set_option("theoref", cmdline.isset("theoref"));
  options.set_option("force", cmdline.isset("force"));
  options.set_option("custom", cmdline.get_value("custom"));
  options.set_option("heuristic", cmdline.get_value("heuristic"));
  if (cmdline.isset("bitwidth")) {
    options.set_option("bitwidth", cmdline.get_value("bitwidth"));
  } else {
    options.set_option("bitwidth", 8);
  }
  if (cmdline.isset("dump-query"))
      options.set_option("dump-query", true);

  if (cmdline.isset("dump-query-name")) {
      options.set_option("dump-query-name", cmdline.get_value("dump-query-name"));
  } else { // Set to empty string and let osmt choose the name
      options.set_option("dump-query-name", "");
  }

  // always check assertions
  options.set_option("assertions", true);

  // always use assumptions
  options.set_option("assumptions", true);

  // Use basic check as defualt
  options.set_option("type-constraints", 1);

  if(cmdline.isset("logic")) {
    options.set_option("logic", cmdline.get_value("logic"));
  } else { // Set to qfuf - defualt
    options.set_option("logic", "qfuf"); 
  }

  
  // If not partitions - no itp too, going back to pure cbcm
  if(cmdline.isset("no-partitions"))
      options.set_option("no-itp", true);
  
  if (cmdline.isset("check-itp")) {
    options.set_option("check-itp", cmdline.get_value("check-itp"));
  }
  if (cmdline.isset("itp-algorithm")) { // In Help Menu
    options.set_option("itp-algorithm", cmdline.get_value("itp-algorithm"));
  }
  if (cmdline.isset("itp-uf-algorithm")) { // In Help Menu
    options.set_option("itp-uf-algorithm", cmdline.get_value("itp-uf-algorithm"));
  }
  if (cmdline.isset("itp-lra-algorithm")) { // In Help Menu
    options.set_option("itp-lra-algorithm", cmdline.get_value("itp-lra-algorithm"));
  }
  if (cmdline.isset("itp-lra-factor")) { // In Help Menu
    options.set_option("itp-lra-factor", cmdline.get_value("itp-lra-factor"));
  }
  //if (cmdline.isset("part-itp")) {
  //  options.set_option("part-itp", cmdline.get_value("part-itp"));
  //}
  //if (cmdline.isset("proof-trans")) {
  //  options.set_option("proof-trans", cmdline.get_value("proof-trans"));
  //}
  if (cmdline.isset("unwind")) {
    options.set_option("unwind", cmdline.get_value("unwind"));
  } else { // Set to max - KE: find a better way to do so
    options.set_option("unwind", "4294967295"); 
  }
  //if (cmdline.isset("unwindset")) {
  //  options.set_option("unwindset", cmdline.get_value("unwindset"));
  //}
  if (cmdline.isset("type-constraints")) { // In Help Menu
    options.set_option("type-constraints", cmdline.get_value("type-constraints"));
  }
  if (cmdline.isset("claimset")) {
    options.set_option("claimset", cmdline.get_value("claimset"));
  }
  if (cmdline.isset("claims-opt")) { // In Help Menu
    options.set_option("claims-opt", cmdline.get_value("claims-opt"));
  }
  //if (cmdline.isset("do-upgrade-check")) { // KE: not working
  //  options.set_option("do-upgrade-check", cmdline.get_value("do-upgrade-check"));
  //}
  if (cmdline.isset("save-summaries")) {
    options.set_option("save-summaries", cmdline.get_value("save-summaries"));
  } else {
    options.set_option("save-summaries", "__summaries");
  }
  if (cmdline.isset("save-omega")) {
    options.set_option("save-omega", cmdline.get_value("save-omega"));
  } else {
    options.set_option("save-omega", "__omega");
  }
  if (cmdline.isset("load-summaries")) {
    options.set_option("load-summaries", cmdline.get_value("load-summaries"));
  } else {
    options.set_option("load-summaries", "__summaries");
  }
  if (cmdline.isset("load-omega")) {
    options.set_option("load-omega", cmdline.get_value("load-omega"));
  } else {
    options.set_option("load-omega", "__omega");
  }
  if (cmdline.isset("save-change-impact")) {
    options.set_option("save-change-impact", cmdline.get_value("save-change-impact"));
  } else {
    options.set_option("save-change-impact", "__calltree.xml");
  }
  //if (cmdline.isset("reduce-proof-time")) {
  //  options.set_option("reduce-proof-time", cmdline.get_value("reduce-proof-time"));
  //}
  if (cmdline.isset("reduce-proof-graph")) { // In Help Menu
    options.set_option("reduce-proof-graph", cmdline.get_value("reduce-proof-graph"));
  }
  if (cmdline.isset("reduce-proof-loops")) { // In Help Menu
    options.set_option("reduce-proof-loops", cmdline.get_value("reduce-proof-loops"));
  }
  if (cmdline.isset("random-seed")) {
    options.set_option("random-seed", cmdline.get_value("random-seed"));
  }
  if (cmdline.isset("color-proof")) {
    options.set_option("color-proof", cmdline.get_value("color-proof"));
  } else {
    options.set_option("color-proof", "-1");
  }
  if (cmdline.isset("verbose-solver")) {
    options.set_option("verbose-solver", cmdline.get_value("verbose-solver"));
  }
  //if (cmdline.isset("refine-mode")) {
  //  options.set_option("refine-mode", cmdline.get_value("refine-mode"));
  //}
  //if (cmdline.isset("init-mode")) {
  //  options.set_option("init-mode", cmdline.get_value("init-mode"));
  //}
}
