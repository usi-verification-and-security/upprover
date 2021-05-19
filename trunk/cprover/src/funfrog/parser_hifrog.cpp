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
      "HiFrog [version " << HIFROG_VERSION << " uses CPROVER " << CPROVER_VERSION_HIFROG << "]"
      "\n"
      "Usage:                         Purpose:\n"
      "\n"
      " hifrog [-?] [-h] [--help]     show help\n"
      " hifrog [options] <logic> <file>       run on C `file'\n"
      "\nGeneral Purpose options:\n"
      "--version                      show version information\n"
      "--logic <logic>                [qfuf, qfcuf, qflra, qflia, prop] if not present qfuf is used\n"
      "--sum-theoref                  for all the claims, automatically selects the lightest possible theory\n"
      "                               and gradually strengthen it\n"
      "--save-summaries <filename>    save collected function summaries\n"
      "                               to the given file\n"
      "--load-summaries <filename>    load function summaries\n"
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
      "--no-itp                       do not construct summaries (just report SAFE/BUG)\n"
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
      "                                 0 - Farkas (the default),\n"
      "                                 2 - Dual Farkas,\n"
      "                                 3 - custom factor,\n"
      "                                 4 - Decomposing Farkas,\n"
      "                                 5 - Dual decomposing Farkas.\n"
      "--itp-lra-factor               LRA interpolation strength factor:\n"
      "                               must be a fraction in the interval [0,1)\n"
      "--verbose-solver <N>           set the verbosity to N\n"
      "                                 1 - print statistics on the inerpolating solver,\n"
      "                                 2 - get the interpolant directly in the console,\n"
      "--reduce-proof                 enable Proof Reduction\n"
      "--reduce-proof-graph           number of graph traversals per reduction iteration\n"
      "--reduce-proof-loops           number of reduction iterations\n"
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

\*******************************************************************/

int parser_hifrogt::doit()
{
    if (config.set(cmdline))
    {
        usage_error();
        exit(1);
    }
    
    register_languages();
    set_options(cmdline);
    
    //stream_message_handlert mh(std::cout);
    set_message_handler(ui_message_handler);
    
    eval_verbosity();
    
    
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
    
    //namespacet ns (symbol_table);
    cbmc_status_interface(std::string("Loading `")+cmdline.args[0]+"' ...");
    auto before=timestamp();
    
    
    goto_modelt goto_model;  //1st goto program associated with the original inputFile for normal use of hifrog & bootstraping.
    if(get_goto_program(goto_model, cmdline)) {    //obtains 1st goto-program
        return 6;
    }
    
    auto after=timestamp();
    cbmc_status_interface(std::string("    LOAD Time: ") + std::to_string(time_gap(after,before)) + std::string(" sec."));
    
    
    if (cmdline.isset("show-symbol-table"))
    {
        show_symbol_table(goto_model, ui_message_handler.get_ui());
        return 0;
    }
    
    if(cmdline.isset("show-goto-functions"))
    {
        
        show_goto_functions(
                goto_model,
                get_message_handler(),
                ui_message_handler.get_ui(),
                false);
        return 0;
    }
    
    if(cmdline.isset("list-templates")) {
        if (options.get_option("logic") != "prop") {
            cbmc_status_interface("Listing templates\n");
            
            UserDefinedSummaryt uds;
            namespacet ns(goto_model.get_symbol_table());
            auto& goto_functions = goto_model.get_goto_functions();
            auto& main = goto_functions.function_map.at(goto_functions.entry_point()).body;
            uds.dump_list_templates(ns, main, goto_functions, options, options.get_unsigned_int_option(HiFrogOptions::UNWIND),
                                    options.get_option(HiFrogOptions::LOGIC), options.get_option(HiFrogOptions::SAVE_FILE));
        }
        else{
            cbmc_error_interface("Error: invalid request for listing the template; it is supported only in LRA and EUF");
        }
        return 0;
    }
    
    calculate_show_claims(goto_model);
    
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
        cbmc_status_interface("Please check --help to revise the user's options ");
        return 1;
    }
    
    cbmc_status_interface("#X: Done.");
    
    return 0;
}
