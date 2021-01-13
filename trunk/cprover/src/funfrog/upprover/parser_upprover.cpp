#include "parser_upprover.h"
#include "funfrog/upprover/summary_validation.h"
/*******************************************************************\

 Function: parser_hifrogt::help

 Inputs:

 Outputs:

 Purpose: display command line help

\*******************************************************************/
void parser_upprovert::help()
{
    std::cout <<"\n"
    "* * *                          UpProver " << UPPROVER_VERSION
    "\n"
    "Usage:                         Purpose:\n"
    "\n"
    " upprover [-?] [-h] [--help]   show help\n"
    " upprover [options] <file>     run on C `file'\n"
    "\nGeneral Purpose options:\n"
    "--version                      show version information\n"
    "--logic <logic>                [qfuf, qflra, qflia, prop] The default is qfuf\n"
    "--save-summaries <filename>    save collected function summaries\n"
    "                               to the given file\n"
    "--load-summaries <filename1,>  load function summaries\n"
    "                               from the given file(s)\n"
    "--show-claims                  output the claims list\n"
    "                               and prints the total number of claims\n"
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
    "--no-cex-model                 skips the cex validator if model cannot be extracted \n"
    #ifdef PRODUCE_PROOF
    "\nUpProver options (Incremental verification of changes):\n"
    "--bootstrapping                prepare for upgrade checking\n"
    "--summary-validation<file>     incremental upgrade check with the specified\n"
    "                               updated version of the program\n"
    "--sanity-check <file1>         sanity checking after bootstrapping for TI property\n"
    "                               usage: <hifrog> <logic> <file1> --sanity-check <file1> \n"
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
    "\n";
}

/*******************************************************************\
 Function: trigger_upprover

 Purpose: making ready for upprover
\*******************************************************************/
void parser_upprovert::trigger_upprover(const goto_modelt &goto_model_old) {
    // a bit of hack; for now slicing does not work in upprover
    options.set_option("no-slicing", true); //disable slicing
    options.set_option("all-claims", true);  //for UpProver this is always true
    
    
    // perform the UpProver (or preparation for that)
    if (cmdline.isset("testclaim") || cmdline.isset("claim") ||
        cmdline.isset("claimset") || cmdline.isset("no-itp")) {
        log.error() <<"UpProver mode does not allow checking specific claims" << messaget::eom;
    }
    
    // bool init_ready = true; // the checks of existence of __omega and upg. version will be later
    if (cmdline.isset("bootstrapping")) {
        check_claims(goto_model_old,
                     claim_checkmap,
                     claim_numbers,
                     options,
                     ui_message_handler,
                     claim_user_nr);
        return;
    }

//2nd phase
    if (cmdline.isset("summary-validation") || cmdline.isset("sanity-check")) {
        std::string new_filepath;
        if (cmdline.isset("sanity-check")) {
            new_filepath = cmdline.get_value("sanity-check");
        }
        else {
            new_filepath = cmdline.get_value("summary-validation");
        }
        status() << std::string("Loading a changed version: `") + new_filepath + "' ...\n";
        
        auto old_args = cmdline.args;  //old file path
        cmdline.args = {new_filepath};
        goto_modelt goto_model_new;     // 2nd goto model associated with changed version
        
        if (get_goto_program(goto_model_new, options, cmdline, ui_message_handler)) {
            return;
        }
    
        launch_upprover(
                // OLD!
                goto_model_old,
                // NEW!
                goto_model_new,
                options,
                ui_message_handler);
        
    }
}

/*******************************************************************

 Function: parsert::doit

 Purpose: invoke main modules

\*******************************************************************/

int parser_upprovert::doit()
{
    if(cmdline.isset("version"))
    {
        std::cout << UPPROVER_VERSION << '\n';
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
        log.error() << "Please provide an input file" << messaget::eom;
        return CPROVER_EXIT_INCORRECT_TASK;
    }
    else if (cmdline.args.size()>1)
    {
        log.error() << "Please give exactly one source file" << messaget::eom;
        return CPROVER_EXIT_INCORRECT_TASK;
    }
    
    messaget::eval_verbosity(
            cmdline.get_value("verbosity"), messaget::M_STATISTICS, ui_message_handler);
    
    //
    // Print a banner
    //
    log.status() << "HiFrog version " << HIFROG_VERSION << " " << sizeof(void *) * 8
                 << "-bit " << configt::this_architecture() << " "
                 << configt::this_operating_system() << messaget::eom;
    
    //
    // Unwinding of transition systems is done by hw-cbmc.
    //
    if(cmdline.isset("module") ||
       cmdline.isset("gen-interface"))
    {
        log.error() << "This version of CBMC has no support for "
                       " hardware modules. Please use hw-cbmc."
                    << messaget::eom;
        return CPROVER_EXIT_USAGE_ERROR;
    }
    register_languages();
    
    // configure gcc, if required
    if(config.ansi_c.preprocessor == configt::ansi_ct::preprocessort::GCC)
    {
        gcc_versiont gcc_version;
        gcc_version.get("gcc");
        configure_gcc(gcc_version);
    }
    
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
                is_goto_binary(cmdline.args[0], ui_message_handler))
        {
            log.error() << "Please give exactly one source file" << messaget::eom;
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
            log.error() << "failed to open input file '" << filename << "'"
                        << messaget::eom;
            return CPROVER_EXIT_INCORRECT_TASK;
        }
        
        std::unique_ptr<languaget> language=
                get_language_from_filename(filename);
        
        if(language==nullptr)
        {
            log.error() << "failed to figure out type of file '" << filename << "'"
                        << messaget::eom;
            return CPROVER_EXIT_INCORRECT_TASK;
        }
        
        language->set_language_options(options);
        language->set_message_handler(ui_message_handler);
        
        log.status() << "Parsing " << filename << messaget::eom;
        
        if(language->parse(infile, filename))
        {
            log.error() << "PARSING ERROR" << messaget::eom;
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
    
    if(cmdline.isset("show-claims") || // will go away
       cmdline.isset("show-properties")) // use this one
    {
        show_properties(goto_model, ui_message_handler);
        return CPROVER_EXIT_SUCCESS;
    }
    
    if(set_properties(goto_model))
        return CPROVER_EXIT_SET_PROPERTIES_FAILED;
    
    calculate_show_claims(goto_model);
    
    if(validate_input_options()) {
        //preparation for UpProver
        if(cmdline.isset("bootstrapping") || cmdline.isset("summary-validation") || cmdline.isset("sanity-check")){
            trigger_upprover(goto_model);
            log.status() << "#X: Done."<< messaget::eom;
            return CPROVER_EXIT_SUCCESS;
        }
        //perform standalone check for stream of assertions in a specific source file
        check_claims(goto_model,
                     claim_checkmap,
                     claim_numbers,
                     options,
                     ui_message_handler,
                     claim_user_nr);
    }
    else {
        log.status() << "Typo! Please see --help to correct the user's options "<< messaget::eom;
        return CPROVER_EXIT_INCORRECT_TASK;
    }
    
    log.status() <<"#X: Done." << messaget::eom;
    
    return CPROVER_EXIT_SUCCESS;
}