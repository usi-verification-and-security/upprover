
#include "parser.h"
#include <remove_asm.h>
#include <util/exit_codes.h>
#include <goto-programs/rewrite_union.h>
/*******************************************************************\

 Function:

 Purpose: Checks if the user has provided a valid input w.r.t to
 logic, claims, availability of interpolation engine, ...


\*******************************************************************/

// ns is changed to goto_model, if using ns check how to change it to goto_model
bool parser_baset::validate_input_options()
{
  // perform standalone check (all the functionality remains the same)
  if(cmdline.isset("claim") &&
     (cmdline.isset("all-claims") || cmdline.isset("claimset") || cmdline.isset("claims-order"))) {
    error_interface("A specific claim cannot be specified if any other claim specification is set.");
    return false;
  }
  
  if(cmdline.isset("all-claims") &&
     (cmdline.isset("claimset") || cmdline.isset("claims-order"))) {
    error_interface("All claims cannot be specified if any other claim specification is set.");
    return false;
  }
  
  if(cmdline.isset("claimset") && cmdline.isset("claims-order")) {
    error_interface("A specific claimset cannot be specified if any other claim specification is set.");
    return false;
  }
  else if(cmdline.isset("claim")) {
    claim_user_nr=atoi(cmdline.get_value("claim").c_str());
    if (claim_user_nr == 0 || claim_user_nr > claim_numbers.size()) {
      error_interface("Testclaim not found.");
      return false;
    }
  }
  else if(!cmdline.isset("all-claims") &&
          !cmdline.isset("claimset") &&
          !cmdline.isset("claims-order") &&
          !cmdline.isset("claim"))
  {
    //fixme in upprover we don't set any claim. if no VCC found (unreachable assertion) report safe
    error_interface("A specific claim is not set, nor any other claim specification is set.");
    status_interface("Warrning: --claim is set to 1.");
    claim_user_nr = 1; // Set as defualt
  }
  
  // option unsupported in cuf or prop
  if ((options.get_option("logic") == "prop") || (options.get_option("logic") == "qfcuf"))
  {
    // Solver type
    if (options.get_option("solver") == "z3") {
      error() << (options.get_option("logic") + " logic in HiFrog is supported only in OpenSMT2""\n") << eom;
      return false; //Unsupported
    }
#ifdef DISABLE_OPTIMIZATIONS
    // lattice refinement - refers to summaries
        if (options.get_option("load-sum-model").size() > 0) {
            error() << ("--load-sum-model option is not supported in theory: " +  options.get_option("logic") + "\n") << eom;
            exit(0); //Unsupported
        }
#endif
  }
  
  // If we set bitwidth, check it sets right, it will be by default 8
  if ((options.get_option("logic") == "qfcuf")  // bitwidth exists only in cuf
      || (options.get_option("load-sum-model").size()!=0)) // Or for latticeref
  {
    unsigned bitwidth = options.get_unsigned_int_option("bitwidth");
    if (!((bitwidth != 0) && !(bitwidth & (bitwidth - 1)))) {
      error_interface("Error: invalid --bitwidth " + cmdline.get_value("bitwidth")
                           + ". Please re-run with bit-width parameter that is a pow of 2!");
      return false;
    } else if (bitwidth > 32) {
      status_interface("Warrning: --bitwidth larger than 32-bits has only partial support in qfcuf");
    }
  }
  
  // For now till create a proper solution in OpenSMT
  if (options.get_option("logic") == "qflia") {
    options.set_option("no-itp", true);
  }
  
  return true;
}

/*******************************************************************

 Function: parsert::set_default_options

 MB: taken from cbmc_parse_optionst::set_default_options;
 especially simplify must be set to true

\*******************************************************************/
void parser_baset::set_default_options(optionst &options)
{
  // Default true
  options.set_option("assertions", true);   // always check assertions
  options.set_option("assumptions", true);  // always use assumptions
  options.set_option("built-in-assertions", true);
  options.set_option("pretty-names", true);
  options.set_option("propagation", true);
  options.set_option("sat-preprocessor", true);
  options.set_option("simplify", true);
  options.set_option("simplify-if", true);
  
  // Other default
  options.set_option("arrays-uf", "auto");
}

/*******************************************************************
General Note:
 A goto_functionst object contains a set of GOTO programs. Note the
counter-intuitive naming: `goto_functionst` instances are the top level
structure representing the program and contain `goto_programt` instances
which represent the individual functions.

An instance of  goto_programt is effectively a list of
instructions (a nested class called goto_programt::instructiont).

Purpose: Get a Goto-Program; initialize_goto_model does the whole job.

Note: In CBMC5.12 this method is static, but UpProver needs non-static
to have two goto-programs at the same time

GOTO programs are commonly produced using the `initialize_goto_model` function,
which combines the complete process from command-line arguments specifying
source code files, through parsing and generating a symbol table, to finally
producing GOTO functions.
Purpose: Get a Goto Program; initialize_goto_model does the whole job
\*******************************************************************/
int parser_baset::get_goto_program( goto_modelt &goto_model, cmdlinet &cmdline)
{
  if(cmdline.args.empty())
  {
    error() << "Please provide a program to verify" << eom;
    return CPROVER_EXIT_INCORRECT_TASK;
  }
  
  try
  {
    //goto model is obtained completely
    goto_model = initialize_goto_model(cmdline.args, get_message_handler(), options);
  
    if(cmdline.isset("show-symbol-table"))
    {
      show_symbol_table(goto_model, ui_message_handler);
      return CPROVER_EXIT_SUCCESS;
    }
    
    if(process_goto_program(goto_model, cmdline, options, *this ))
      return CPROVER_EXIT_INTERNAL_ERROR;
  
    // show it?
    if(cmdline.isset("show-loops"))
    {
      show_loop_ids(ui_message_handler.get_ui(), goto_model);
      return CPROVER_EXIT_SUCCESS;
    }
  
    // show it?
    if(
        cmdline.isset("show-goto-functions") ||
        cmdline.isset("list-goto-functions"))
    {
      show_goto_functions(
          goto_model,
          ui_message_handler,
          ui_message_handler.get_ui(),
          cmdline.isset("list-goto-functions"));
      return CPROVER_EXIT_SUCCESS;
    }
  
    status() << config.object_bits_info() << eom;
  }

  catch(incorrect_goto_program_exceptiont &e)
  {
    error() << e.what() << eom;
    return CPROVER_EXIT_EXCEPTION;
  }

  catch(const char *e)
  {
    error() << e << eom;
    return CPROVER_EXIT_EXCEPTION;
  }

  catch(const std::string &e)
  {
    error() << e << eom;
    return CPROVER_EXIT_EXCEPTION;
  }

  catch(int e)
  {
    error() << "Numeric exception : " << e << eom;
    return CPROVER_EXIT_EXCEPTION;
  }

  catch(const std::bad_alloc &)
  {
    error() << "Out of memory" << eom;
    return CPROVER_EXIT_INTERNAL_OUT_OF_MEMORY;
  }
  
  return -1; // no error, continue
}


/*******************************************************************\
 
 Function:

 Purpose:

\*******************************************************************/

unsigned parser_baset::count(const goto_functionst &goto_functions) const
{
  unsigned long c=0;
  for(goto_functionst::function_mapt::const_iterator it =
      goto_functions.function_map.begin();
      it!=goto_functions.function_map.end();
      it++)
  {
    c += it->second.body.instructions.size();
  }
  
  std::cout << "    Instruction count: " << c << std::endl;
  
  return c;
}

/*******************************************************************\
 
 Function:

 Purpose:

\*******************************************************************/

unsigned parser_baset::count(const goto_programt &goto_program) const
{
  std::cout << "    Instruction count: " << goto_program.instructions.size()
            << std::endl;
  return goto_program.instructions.size();
}


/*******************************************************************\

 Function:

 Purpose: Calculate claim numbers, and print them on demand

\*******************************************************************/
void parser_baset::calculate_show_claims(goto_modelt & goto_model) {
  
  get_claims(goto_model.goto_functions, claim_checkmap, claim_numbers);
  status_interface("Total number of claims in program...(" + std::to_string(claim_numbers.size()) + ")");
  
  if (cmdline.isset("show-claims") || cmdline.isset("show-properties")) {
    show_properties(goto_model, get_message_handler(), ui_message_handler.get_ui());
    status_interface("#Total number of claims: " + std::to_string(claim_numbers.size()));
    exit(0);
  }
  if (cmdline.isset("claims-opt"))
    store_claims(claim_checkmap, claim_numbers);
}

/*******************************************************************\
 
 Function:

 Purpose:

\*******************************************************************/
void parser_baset::set_options_All(const cmdlinet &cmdline)
{
  set_default_options(options);
  
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
  status() << "\n*** NO INTERPOLATION MODE, NOT USING SUMMARY FILES (DPRODUCE_PROOF is off) ***\n" << eom;
#endif
#ifdef DISABLE_OPTIMIZATIONS
  if (cmdline.isset("dump-SSA-tree"))
        options.set_option("dump-SSA-tree", true);
    
    if (cmdline.isset("dump-pre-query"))
        options.set_option("dump-pre-query", true);
    
    if (cmdline.isset("dump-query"))
        options.set_option("dump-query", true);
    
    if (cmdline.isset("dump-query-name")) {
        options.set_option("dump-query-name", cmdline.get_value("dump-query-name"));
    } else { // Set a default name in case no name was provided by user
        options.set_option("dump-query-name", "query_default");
    }
    
    status() << "\n*** DEBUG MODE ON: QUERIES DUMP OPTIONS ARE ON (DDISABLE_OPTIMIZATIONS is on) ***\n" << eom;
#else
  status() << "\n*** EXECUTE WITH OPTIMIZATIONS (DDISABLE_OPTIMIZATIONS is off) ***\n" << eom;
#endif
  
  if (cmdline.isset("solver")) {
    options.set_option(HiFrogOptions::SOLVER, cmdline.get_value("solver"));
  } else {
    options.set_option(HiFrogOptions::SOLVER, "osmt");
  }
  options.set_option("no-partitions", cmdline.isset("no-partitions"));
  options.set_option("no-assert-grouping", cmdline.isset("no-assert-grouping"));
  options.set_option("no-summary-optimization", cmdline.isset("no-summary-optimization"));
  options.set_option("tree-interpolants", cmdline.isset("tree-interpolants"));
  options.set_option("check-itp", cmdline.isset("check-itp"));
  options.set_option("no-error-trace", cmdline.isset("no-error-trace"));
  //options.set_option("list-templates", cmdline.isset("list-templates")); // FIXME
  options.set_option("no-cex-model", cmdline.isset("no-cex-model"));
  options.set_option("no-sum-refine", cmdline.isset("no-sum-refine"));
  options.set_option("reduce-proof", cmdline.isset("reduce-proof"));
  options.set_option("partial-loops", cmdline.isset("partial-loops"));

#ifdef PRODUCE_PROOF
//*********** Combination of Summary and Theory Refinement option***********
  options.set_option("sum-theoref", cmdline.isset("sum-theoref"));

//*********** UpProver options ***********
  options.set_option("bootstrapping", cmdline.isset("bootstrapping"));
  if (cmdline.isset("summary-validation")) {
    options.set_option("summary-validation", cmdline.get_value("summary-validation"));
  }
  options.set_option("bootstrapping", cmdline.isset("bootstrapping"));
  
  //"sanity-check" behaves as if doing upgrade checking of 2 same programs, so we trigger summary-validation internally
  if (cmdline.isset("sanity-check")) {
    options.set_option("sanity-check", cmdline.isset("sanity-check"));
    options.set_option("summary-validation", true);
    options.set_option("summary-validation", cmdline.get_value("sanity-check"));
//N.B. if(options.is_set("summary-validation")) At this point returns true
// but
//     if(cmdline.isset("summary-validation") still returns false!
  }
#endif

//*********** Theory Refinement Options ***********
  options.set_option("theoref", cmdline.isset("theoref"));
  options.set_option("force", cmdline.isset("force"));
  options.set_option("custom", cmdline.get_value("custom"));
  
  if (cmdline.isset("bitwidth")) {
    options.set_option("bitwidth", cmdline.get_value("bitwidth"));
  } else {
    options.set_option("bitwidth", 8); //the default bit-width for theoref
  }
  
  if (cmdline.isset("heuristic")) {
    options.set_option("heuristic", cmdline.get_value("heuristic"));
  } else {
    options.set_option("heuristic", 4);
  }//End of theory refinement Options ***********

//*********** defualt basic constraints on numerical data type***********
  options.set_option("type-constraints", 1);
  options.set_option("type-byte-constraints", 0);
  
  if(cmdline.isset("logic")) {
    options.set_option("logic", cmdline.get_value("logic"));
  } else { // Set to qfuf - defualt
    options.set_option("logic", "qfuf");
  }
  
  // If not partitions - no itp too, going back to pure cbcm
  if(cmdline.isset("no-partitions")) {
    options.set_option("no-itp", true);
  }
  
  // KE: keep it for theoref, else won't work properly
  if(cmdline.isset("theoref")) {
    options.set_option("no-itp", true);
    options.set_option("partial-loops", false);
  }
  
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
    options.set_option("unwind", std::to_string(std::numeric_limits<unsigned int>::max()));
  }
  //if (cmdline.isset("unwindset")) {
  //  options.set_option("unwindset", cmdline.get_value("unwindset"));
  //}
  if (cmdline.isset("type-constraints")) { // In Help Menu
    options.set_option("type-constraints", cmdline.get_value("type-constraints"));
  }
  if (cmdline.isset("type-byte-constraints")) { // In Help Menu
    options.set_option("type-byte-constraints", cmdline.get_value("type-byte-constraints"));
  }
  if (cmdline.isset("claimset")) {
    options.set_option("claimset", cmdline.get_value("claimset"));
  }
  if (cmdline.isset("claims-opt")) { // In Help Menu
    options.set_option("claims-opt", cmdline.get_value("claims-opt"));
  }
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
  if (cmdline.isset("load-sum-model")) {
    options.set_option("load-sum-model", cmdline.get_value("load-sum-model"));
    options.set_option("no-itp", true); // Remove after fix the issue with lattice facts dumped into the summary of the code
  } else {
    options.set_option("load-sum-model","");
  }
  //if(cmdline.isset("sum-model-single-UNSAT"))
  //  options.set_option("sum-model-single-UNSAT", true);
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
  } else {
    options.set_option("reduce-proof-graph", 3);
  }
  if (cmdline.isset("reduce-proof-loops")) { // In Help Menu
    options.set_option("reduce-proof-loops", cmdline.get_value("reduce-proof-loops"));
  } else {
    options.set_option("reduce-proof-loops", 2);
  }
  if (cmdline.isset("random-seed")) {
    options.set_option("random-seed", cmdline.get_value("random-seed"));
  } else {
    options.set_option("random-seed", "1");
  }
  if (cmdline.isset("color-proof")) {
    options.set_option("color-proof", cmdline.get_value("color-proof"));
  } else {
    options.set_option("color-proof", "-1");
  }
  if (cmdline.isset("verbose-solver")) {
    options.set_option("verbose-solver", cmdline.get_value("verbose-solver"));
  } else {
    options.set_option("verbose-solver", "0");
  }
  //options.set_option("simplify-if", false); // Try to avoid compications with if
  //if (cmdline.isset("refine-mode")) {
  //  options.set_option("refine-mode", cmdline.get_value("refine-mode"));
  //}
  //if (cmdline.isset("init-mode")) {
  //  options.set_option("init-mode", cmdline.get_value("init-mode"));
  //}
}

/*******************************************************************\
 
 Function:

 Purpose:

 Note: Taken from void cbmc_parse_optionst::eval_verbosity(),
       Update if needed (once upgrade cprover)

\*******************************************************************/
void parser_baset::eval_verbosity()
{
  // this is our default verbosity
  unsigned int v=messaget::M_STATISTICS;
  
  if(cmdline.isset("verbosity"))
  {
    v=unsafe_string2unsigned(cmdline.get_value("verbosity"));
    if(v>10)
      v=10;
  }
  
  ui_message_handler.set_verbosity(v);
}

/*******************************************************************

 Function: standalone process_goto_program

Note: This function used to be a member function of parser_baset class,
 but in order to be reusebale for several goto_model we made it standalone.

 Note: KE: Previously was inspired by: cbmc_parseoptionst::process_goto_program

\*******************************************************************/
bool process_goto_program(goto_modelt &goto_model,const cmdlinet &cmdline,
                          const optionst &options, messaget &msg)
{
  try
  {
    // Remove inline assembler; this needs to happen before
    // adding the library.
    remove_asm(goto_model);
    // Only to prop logic
//        if (cmdline.isset(HiFrogOptions::LOGIC.c_str()))
//        {   //TODO extend it to other logics as well
//            if (cmdline.get_value(HiFrogOptions::LOGIC.c_str()) == "prop")
//            {
    // add the library
//                 link_to_library(
//                         goto_model, msg.get_message_handler(), cprover_cpp_library_factory);
//                 link_to_library(
//                         goto_model, msg.get_message_handler(), cprover_c_library_factory);
//              }
//            else
//            {
//                msg.status() << "Ignoring CPROVER library" << msg.eom;
//            }
//        }
//        else
//        {
    msg.status() << "Ignoring CPROVER library" << msg.eom;
//        }
    
    if (cmdline.isset("string-abstraction"))
      string_instrumentation(
          goto_model, msg.get_message_handler());
    
    msg.status() << "Removal of function pointers and virtual functions" << msg.eom;
    remove_function_pointers(
        msg.get_message_handler(),
        goto_model,
        false); // HiFrog doesn't have pointer check, set the flag to false always
    // Java virtual functions -> explicit dispatch tables:
    remove_virtual_functions(goto_model);
    
    mm_io(goto_model);
    
    // instrument library preconditions
    instrument_preconditions(goto_model);
    
    // remove returns, gcc vectors, complex
    // remove_returns(symbol_table, goto_functions); //KE: causes issues with hifrog/upprover
    remove_vector(goto_model);
    remove_complex(goto_model);
    rewrite_union(goto_model);
    
    // add generic checks
    msg.status() << "Generic Property Instrumentation" << msg.eom;
    goto_check(options, goto_model);
    
    //HIFROG: We remove built-ins (e.g., CPROVER_rounding_mode) from smt logics
    //For handling floats symbol CPROVER_rounding_mode should be added only in bv
    if (cmdline.isset(HiFrogOptions::LOGIC.c_str()))
    {
      if (cmdline.get_value(HiFrogOptions::LOGIC.c_str()) == "prop")
      {
        adjust_float_expressions(goto_model);
      }
    }
    
    if (cmdline.isset("string-abstraction"))
    {
      msg.status() << "String Abstraction" << msg.eom;
      string_abstraction(
          goto_model,
          msg.get_message_handler());
    }
    
    // add failed symbols
    // needs to be done before pointer analysis
    add_failed_symbols(goto_model.symbol_table);
    
    //use CPROVER goto-instrument style to unwind the loops in the pre-processing
    //before performing symbolic execution in symex
    //The reason is we want to differentiate each function call inside a loop so that later
    //each of which would have a single function summary.
    if (cmdline.isset("bootstrapping") || cmdline.isset("summary-validation") || cmdline.isset("sanity-check"))
    {
      unwindsett unwindset;
      unwindset.parse_unwind(cmdline.get_value(HiFrogOptions::UNWIND.c_str()));
      goto_unwindt goto_unwind;
      //call unwind function
      goto_unwind(goto_model, unwindset, goto_unwindt::unwind_strategyt::ASSUME);
    }
    
    // recalculate numbers, etc.
    goto_model.goto_functions.update();
    
    // add loop ids
    goto_model.goto_functions.compute_loop_numbers();
  
  
    // remove any skips introduced since coverage instrumentation
    remove_skip(goto_model);
    goto_model.goto_functions.update();
    
    //here is not a good place to put the actual unwinding.
    // label the assertions
    // This must be done after adding assertions and
    // before using the argument of the "property" option.
    // Do not re-label after using the property slicer because
    // this would cause the property identifiers to change.
    label_properties(goto_model);
  }
  
  catch(const char *e)
  {
    msg.error() << e <<msg.eom;
    return true;
  }
  
  catch(const std::string &e) //SA
  {
    msg.error() << e <<msg.eom;
    return true;
  }
  
  catch(int e)
  {
    msg.error() << "Numeric exception : " << e << msg.eom;
    return true;
  }
  
  catch(const std::bad_alloc &)
  {
    msg.error() << "Out of memory" <<msg.eom;
    exit(CPROVER_EXIT_INTERNAL_OUT_OF_MEMORY);
    return true;
  }
  
  return false;
}
