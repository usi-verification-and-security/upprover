/*******************************************************************\

 Module: Command Line Parsing

\*******************************************************************/
#include "parser_hifrog.h"
/*******************************************************************\

 Function: parser_hifrogt::help

 Purpose: display command line help

\*******************************************************************/
void parser_hifrogt::help()
{
    std::cout <<"\n"
"* * *                HiFrog " << HIFROG_VERSION
      "\n"
      "Usage:                         Purpose:\n"
      "\n"
      " hifrog [-?] [-h] [--help]     show help\n"
      " hifrog [options] <file>       run on C `file'\n"
      "\nGeneral Purpose options:\n"
      "--version                      show version information\n"
      "--logic <logic>                [qfuf, qfcuf, qflra, qflia, prop] if not present qfuf is used\n"
      "--sum-theoref                  for all the claims, automatically selects the lightest possible theory\n"
      "                               and gradually strengthen it\n"
      "--save-summaries <filename>    save collected function summaries\n"
      "                               to the given file\n"
      "--load-summaries <filename1,>  load function summaries\n"
      "                               from the given file(s)\n"
      "--show-claims                  output the claims list\n"
      "                               and prints the total number of claims\n"
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
      "--partial-loops                do not forbid paths with unsufficient loop unwinding (due to unwind bound)\n"
      "--type-constraints             LRA's and LIA's basic constraints on numerical data type\n"
      "                                 0 - no additional constraints,\n"
      "                                 1 - type constraints on non-deterministic input\n"
      "                                 2 - type constraints on all variables according to their data-type\n"
      "--type-byte-constraints        CUF's basic constraints on numerical data type\n"
      "                                 0 - no additional constraints,\n"
      "                                 1 - type constraints on char data type\n"
      "                                 2 - type constraints on all numerical data types\n"
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
      "--no-partitions                do not use partitions to create the BMC formula\n\n"
      "--solver                       SMT solving option, solver type:\n"
      "                                 osmt - use OpenSMT2 solver,\n"
      "                                 z3   - use Z3 solver\n"
      "\nTheory Refinement options:\n"
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
      "--bitwidth <n>                 bitwidth for the CUF BV mode and CEX Validator\n\n"
      "--no-cex-model                 skips the cex validator if model cannot be extracted \n"
      #ifdef PRODUCE_PROOF
      "--save-omega <filename>        save the last used substitution scenario\n"
      "                               to the given file\n"
      "--load-omega <filename>        load substitution scenario\n"
      "\nInterpolation, and Proof Reduction options in SMT:\n"

      "--itp-algorithm                propositional interpolation algorithm: \n"
      "                                 0 - McMillan_s,\n"
      "                                 1 - Pudlak,\n"
      "                                 2 - McMillan_w\n"
      "--itp-uf-algorithm             EUF interpolation algorithm:\n"
      "                                 0 - Strong,\n"
      "                                 2 - Weak,\n"
      "                                 3 - Random\n"
      "--itp-lra-algorithm            LRA interpolation algorithm:\n"
      "                                 0 - Strong,\n"
      "                                 2 - Weak\n"
      "                                 3 - custom factor.\n"
      "--itp-lra-factor               LRA interpolation strength factor:\n"
      "                               must be a fraction in the interval [0,1)\n"
      "--reduce-proof                 enable Proof Reduction\n"
      "--reduce-proof-graph           number of graph traversals per reduction iteration\n"
      "--reduce-proof-loops           number of reduction iterations\n"
      #endif

      #ifdef DISABLE_OPTIMIZATIONS
      "\nDebug Options:(Options Valid Only in SMT-Based Verification)\n"
//"--list-templates               dump the templates of the functions for user-defined summaries\n"
"--dump-SSA-tree                ask a dump of SSA form in smt2 format\n" //the default is __SSA__dump_1.smt2
"--dump-pre-query               ask HiFrog to dump the smtlib query before sending to solver\n" //the default is __preq__dump_1.smt2
"--dump-query                   ask OpenSMT to dump the smtlib query before solving\n" //by default dumps into _dump-1.smt2 file.
"--dump-query-name <base>       base name for the files where queries are dumped\n"
      #endif
      "\nProgram representations:\n"
      "--show-symbol-table             show symbol table\n"
      "--show-goto-functions           show goto functions(show goto program)\n"
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

/*******************************************************************

 Function:

 Purpose: invoke main modules
 Taken from CBMC 5.12

\*******************************************************************/

int parser_hifrogt::doit()
{
    if(cmdline.isset("version"))
    {
        std::cout << HIFROG_VERSION << '\n';
        return CPROVER_EXIT_SUCCESS;
    }
    //
    // command line options
    //
    optionst options;
    set_options(cmdline); //HiFrog/UpProver specific; removed in CBMC5.12
    
    get_command_line_options(options);
    
    //customized
    if(cmdline.args.empty())
    {
        error() << "Please provide an input file" << messaget::eom;
        return CPROVER_EXIT_INCORRECT_TASK;
    }
    else if (cmdline.args.size()>1)
    {
        error() << "Please give exactly one source file" << messaget::eom;
        return CPROVER_EXIT_INCORRECT_TASK;
    }
    
    messaget::eval_verbosity(
            cmdline.get_value("verbosity"), messaget::M_STATISTICS, ui_message_handler);
    
    //
    // Print a banner
    //
    status() << "HiFrog version " << HIFROG_VERSION << " " << sizeof(void *) * 8
                 << "-bit " << configt::this_architecture() << " "
                 << configt::this_operating_system() << messaget::eom;
    
    //
    // Unwinding of transition systems is done by hw-cbmc.
    //
    if(cmdline.isset("module") ||
       cmdline.isset("gen-interface"))
    {
        error() << "This version of CBMC has no support for "
                       " hardware modules. Please use hw-cbmc."
                    << messaget::eom;
        return CPROVER_EXIT_USAGE_ERROR;
    }
    register_languages();
    
    if(cmdline.isset("test-preprocessor"))
        return test_c_preprocessor(ui_message_handler)
               ? CPROVER_EXIT_PREPROCESSOR_TEST_FAILED
               : CPROVER_EXIT_SUCCESS;
    
    if(cmdline.isset("preprocess"))
    {
        preprocessing(options);
        return CPROVER_EXIT_SUCCESS;
    }
    
    if(cmdline.isset("show-parse-tree"))
    {
        if(
                cmdline.args.size() != 1 ||
                is_goto_binary(cmdline.args[0]))
        {
            error() << "Please give exactly one source file" << messaget::eom;
            return CPROVER_EXIT_INCORRECT_TASK;
        }
        
        std::string filename=cmdline.args[0];

#ifdef _MSC_VER
        std::ifstream infile(widen(filename));
#else
        std::ifstream infile(filename);
#endif
        
        if(!infile)
        {
            error() << "failed to open input file '" << filename << "'"
                        << messaget::eom;
            return CPROVER_EXIT_INCORRECT_TASK;
        }
        
        std::unique_ptr<languaget> language=
                get_language_from_filename(filename);
        
        if(language==nullptr)
        {
            error() << "failed to figure out type of file '" << filename << "'"
                        << messaget::eom;
            return CPROVER_EXIT_INCORRECT_TASK;
        }
        
        language->set_language_options(options);
        language->set_message_handler(ui_message_handler);
        
        status() << "Parsing " << filename << messaget::eom;
        
        if(language->parse(infile, filename))
        {
            error() << "PARSING ERROR" << messaget::eom;
            return CPROVER_EXIT_INCORRECT_TASK;
        }
        
        language->show_parse(std::cout);
        return CPROVER_EXIT_SUCCESS;
    }
    
    //1st goto program of the original inputFile for standalone HiFrog & bootstraping UpProver.
    goto_modelt goto_model;
    //get 1st goto-program
    
    int get_goto_program_ret =
            get_goto_program(goto_model, options, cmdline, ui_message_handler);
    
    if(get_goto_program_ret!=-1)
        return get_goto_program_ret;
    
//    if(cmdline.isset("show-claims") || // will go away
//       cmdline.isset("show-properties")) // use this one
//    {
//        show_properties(goto_model, ui_message_handler);
//        return CPROVER_EXIT_SUCCESS;
//    }
    
    if(set_properties(goto_model))
        return CPROVER_EXIT_SET_PROPERTIES_FAILED;
    

    
    //stream_message_handlert mh(std::cout);
    //set_message_handler(ui_message_handler);
    
    if(cmdline.isset("list-templates")) {
        if (options.get_option("logic") != "prop") {
            status() <<"Listing templates\n"<< messaget::eom;
            
            UserDefinedSummaryt uds;
            namespacet ns(goto_model.get_symbol_table());
            auto& goto_functions = goto_model.get_goto_functions();
            auto& main = goto_functions.function_map.at(goto_functions.entry_point()).body;
            uds.dump_list_templates(ns, main, goto_functions, options, options.get_unsigned_int_option(HiFrogOptions::UNWIND),
                                    options.get_option(HiFrogOptions::LOGIC), options.get_option(HiFrogOptions::SAVE_FILE), ui_message_handler);
        }
        else{
            error() <<"Error: invalid request for listing the template; it is supported only in LRA and EUF"<< messaget::eom;
        }
        return CPROVER_EXIT_SUCCESS;
    }
    
    //calculate_show_claims(goto_model);
    
    if(validate_input_options()) {
        //perform standalone check for stream of assertions in a specific source file
        check_claims(goto_model,
                     claim_checkmap,
                     claim_numbers,
                     options,
                     ui_message_handler,
                     claim_user_nr);
    }
    else {
        status() << "Typo! Please see --help to correct the user's options "<< messaget::eom;
        return CPROVER_EXIT_INCORRECT_TASK;
    }
    
    status() <<"#X: Done." << messaget::eom;
    
    return CPROVER_EXIT_SUCCESS;
}