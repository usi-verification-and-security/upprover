/*******************************************************************\

 Module: Command Line Parsing

\*******************************************************************/
#include "parser_hifrog.h"

#include <util/config.h>
#include <iostream>
#include <sys/time.h>
#include <sys/stat.h>
#ifndef _WIN32
#include <sys/resource.h>
#else
#include <io.h>
#endif

#include <util/std_expr.h>
#include <util/arith_tools.h>
#include <util/prefix.h>

#include <goto-programs/adjust_float_expressions.h>
#include <goto-programs/goto_convert_functions.h>
#include <goto-programs/remove_function_pointers.h>
//#include <goto-programs/remove_returns.h> // KE: never include this header
#include <goto-programs/remove_vector.h>
#include <goto-programs/remove_complex.h>
#include <goto-programs/remove_asm.h>
#include <goto-programs/remove_unused_functions.h>
#include <goto-programs/show_properties.h>
#include <goto-programs/set_properties.h>
#include <goto-programs/read_goto_binary.h>
#include <goto-programs/string_abstraction.h>
#include <goto-programs/string_instrumentation.h>

#include <goto-symex/rewrite_union.h>

#include <goto-instrument/full_slicer.h>
#include <goto-instrument/nondet_static.h>

#include <pointer-analysis/add_failed_symbols.h>

#include <analyses/goto_check.h>
#include <langapi/mode.h>

#include <ansi-c/cprover_library.h>

#include <cpp/cprover_library.h>

#include "check_claims.h"
#include "version.h"
#include <goto-programs/link_to_library.h> // Only for prop logic!
#include <goto-programs/mm_io.h>
#include <goto-programs/goto_inline.h>
#include <goto-programs/remove_virtual_functions.h>
#include <goto-programs/remove_skip.h>
#include <goto-programs/goto_functions.h>
#include <goto-programs/initialize_goto_model.h>
#include <goto-programs/read_goto_binary.h>
#include <goto-programs/instrument_preconditions.h>
#include <util/string2int.h>
#include <langapi/language_ui.h>
#include <goto-programs/show_symbol_table.h>
#include <goto-programs/show_goto_functions.h>
#include <goto-programs/show_properties.h>
#include "UserDefinedSummary.h" // TODO: doesn't work yet, only contains original code
#include <limits>
#include <funfrog/utils/naming_helpers.h>

#include <funfrog/utils/time_utils.h>
#include "funfrog/evolcheck/upgrade_checker.h"

/*******************************************************************

 Function: parser_hifrogt::parser_hifrogt

 Purpose: constructor

 \*******************************************************************/

parser_hifrogt::parser_hifrogt(int argc, const char **argv):
  parse_options_baset(FUNFROG_OPTIONS, argc, argv),
  xml_interfacet(cmdline),
  //messaget((std::string("FUNFROG") + FUNFROG_VERSION))
  //messaget(*(new ui_message_handlert(ui_message_handlert::PLAIN, "FUNFROG" FUNFROG_VERSION)))
  messaget(ui_message_handler),
  ui_message_handler(cmdline, "FUNFROG " FUNFROG_VERSION)

{
}
/*******************************************************************

 Function: parser_hifrogt::doit

 Purpose: invoke main modules

\*******************************************************************/

int parser_hifrogt::doit()
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


    goto_modelt goto_model;  //1st goto program associated with the original inputfile for normal use of hifrog & init_upgrade.
    if(get_goto_program(goto_model, cmdline, options)) {    //optained 1st goto-program
		return 6;
	}

    auto after=timestamp();
    cbmc_status_interface(std::string("    LOAD Time: ") + std::to_string(time_gap(after,before)) + std::string(" sec."));


    if (cmdline.isset("show-symbol-table"))
    {
        show_symbol_table(goto_model, ui_message_handler.get_ui());
        return true;
    }

    if(cmdline.isset("show-goto-functions"))
    {

        show_goto_functions(
                goto_model,
                get_message_handler(),
                ui_message_handler.get_ui(),
                false);
        return true;
    }

    calculate_show_claims(goto_model, claim_numbers, claim_checkmap);

    if(validate_input_options(claim_numbers, claim_user_nr)) {
      	//preparation for Upgrade check
    	if(cmdline.isset("init-upgrade-check") || cmdline.isset("do-upgrade-check")){
			trigger_upgrade_check(goto_model);
			cbmc_status_interface("#X: Done.");
        	return 0;
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
    	cbmc_status_interface("Please check --help to revise the user's options ");
    	return 1;
    }

    cbmc_status_interface("#X: Done.");

    return 0;
}
/*******************************************************************

 Function: parser_hifrogt::set_default_options

 MB: taken from cbmc_parse_optionst::set_default_options;
 especially simplify must be set to true

\*******************************************************************/
void parser_hifrogt::set_default_options(optionst &options)
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

 Function:

 Purpose:  Get a Goto Program; initialize_goto_model does the whole job

\*******************************************************************/
bool parser_hifrogt::get_goto_program( goto_modelt &goto_model, cmdlinet &cmdline, optionst &options)
{

  try
  {
    //goto model is obtained completely
    goto_model = initialize_goto_model(cmdline, get_message_handler());

    if(process_goto_program(cmdline, options, goto_model, *this ))
      return true;
  }

  catch(const char *e)
  {
    error() << e << eom;
    return true;
  }

  catch(const std::string &e)
  {
    error() << e << eom;
    return true;
  }

  catch(int e)
  {
    error() << "Numeric exception : " << e << eom;
    return true;
  }

  catch(const std::bad_alloc &)
  {
    cbmc_error_interface("Out of memory");
    return true;
  }

  return false;
}


/*******************************************************************\
  
 Function: 

 Purpose:

\*******************************************************************/

unsigned parser_hifrogt::count(const goto_functionst &goto_functions) const
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

unsigned parser_hifrogt::count(const goto_programt &goto_program) const
{
  std::cout << "    Instruction count: " << goto_program.instructions.size()
    << std::endl;
  return goto_program.instructions.size();
}
/*******************************************************************\
 Function: trigger_upgrade_check

 Purpose: making ready for upgrade checking
\*******************************************************************/
void parser_hifrogt::trigger_upgrade_check(const goto_modelt &goto_model) {
    // a bit of hack; for now slicing does not work in upgrade
    options.set_option("no-slicing", true);
    options.set_option("all-claims", true);  //for upgrade check this is always true
  
  
    // perform the upgrade check (or preparation for that)
    if (cmdline.isset("testclaim") || cmdline.isset("claim") ||
        cmdline.isset("claimset") || cmdline.isset("no-itp")) {
        cbmc_error_interface("Upgrade checking mode does not allow checking specific claims");
    }
  
    // bool init_ready = true; // the checks of existence of __omega and upg. version will be later
    if (cmdline.isset("init-upgrade-check")) {
        check_claims(goto_model,
                 claim_checkmap,
                 claim_numbers,
                 options,
                 ui_message_handler,
                 claim_user_nr);
        return;
    }
//    init_ready = check_initial(ns, goto_functions.function_map[ID_main].body,
//                               goto_functions, options, ui_message_handler, !cmdline.isset("no-progress"));
  
  
//2nd phase
    if (cmdline.isset("do-upgrade-check")) {
        status() << std::string("Loading an upgrade: `") + cmdline.get_value("do-upgrade-check") + "' ...";
    
        auto new_filepath = cmdline.get_value("do-upgrade-check");
        auto old_args = cmdline.args;  //old file path
        cmdline.args = {new_filepath};   //TODO: how about options? make sure you can use the old settings?
        goto_modelt new_model;     // 2nd goto program associated with upgraded_file
    
        if (get_goto_program(new_model, cmdline, options)) {    //2nd go-to program is obtained
            return;
        }
    
    check_upgrade(
		  // OLD!
		  goto_model.goto_functions.function_map.at(ID_main).body, goto_model.goto_functions,
		  // NEW!
		  new_model.goto_functions.function_map.at(ID_main).body, new_model.goto_functions,
		  new_model ,options, ui_message_handler);
    
  }
}
/*******************************************************************\

 Function:

 Purpose: Calculate claim numbers, and print them on demand

\*******************************************************************/
void parser_hifrogt::calculate_show_claims(goto_modelt & goto_model, claim_numberst &claim_numbers, claim_checkmapt &claim_checkmap) {

    get_claims(goto_model.goto_functions, claim_checkmap, claim_numbers);
    cbmc_status_interface("Total number of claims in program...(" + std::to_string(claim_numbers.size()) + ")");

    if (cmdline.isset("show-claims") || cmdline.isset("show-properties")) {
        show_properties(goto_model, get_message_handler(), ui_message_handler.get_ui());
        cbmc_status_interface("#Total number of claims: " + std::to_string(claim_numbers.size()));
        exit(0);
    }
    if (cmdline.isset("claims-opt"))
        store_claims(claim_checkmap, claim_numbers);
}
/*******************************************************************\

 Function:

 Purpose: Checks if the user has provided a valid input w.r.t to
 logic, claims, availability of interpolation engine, ...


\*******************************************************************/

// ns is changed to goto_model, if using ns check how to change it to goto_model
bool parser_hifrogt::validate_input_options(const claim_numberst &claim_numbers, unsigned &claim_user_nr)
{
    // perform standalone check (all the functionality remains the same)
    if(cmdline.isset("claim") &&
        (cmdline.isset("all-claims") || cmdline.isset("claimset") || cmdline.isset("claims-order"))) {
      cbmc_error_interface("A specific claim cannot be specified if any other claim specification is set.");
      return false;
    }

    if(cmdline.isset("all-claims") &&
        (cmdline.isset("claimset") || cmdline.isset("claims-order"))) {
      cbmc_error_interface("All claims cannot be specified if any other claim specification is set.");
      return false;
    }

    if(cmdline.isset("claimset") && cmdline.isset("claims-order")) {
      cbmc_error_interface("A specific claimset cannot be specified if any other claim specification is set.");
      return false;
    }
    else if(cmdline.isset("claim")) {
      claim_user_nr=atoi(cmdline.get_value("claim").c_str());
      if (claim_user_nr == 0 || claim_user_nr > claim_numbers.size()) {
    	cbmc_error_interface("Testclaim not found.");
        return false;
      }
    } 
    else if(!cmdline.isset("all-claims") && 
              !cmdline.isset("claimset") && 
              !cmdline.isset("claims-order") &&
              !cmdline.isset("claim"))
    {
      cbmc_error_interface("A specific claim is not set, nor any other claim specification is set.");
      cbmc_status_interface("Warrning: --claim is set to 1.");
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
        cbmc_error_interface("Error: invalid --bitwidth " + cmdline.get_value("bitwidth")
                + ". Please re-run with bit-width parameter that is a pow of 2!");
        return false;
      } else if (bitwidth > 32) {
        cbmc_status_interface("Warrning: --bitwidth larger than 32-bits has only partial support in qfcuf");   
      }  
    }
    
    // For now till create a proper solution in OpenSMT
    if (options.get_option("logic") == "qflia") {
        options.set_option("no-itp", true);
    }
    
    // FIXME: complete the code inside dump_list_templates
    if(cmdline.isset("list-templates")) {
        if (options.get_option("logic") != "prop") {
            cbmc_error_interface("At present listing summary templates is not functioning.");
            cbmc_status_interface("Listing templates\n");

            // Create the basic formula
            UserDefinedSummaryt user_defined_summary;
            std::string logic = std::string(options.get_option("logic"));

            // dump the summary into a file
            // MB: does not compile in this form, fix later
//        user_defined_summary.dump_list_templates(ns,
//                goto_functions.function_map[goto_functionst::entry_point()].body,
//                goto_functions,
//                options.get_unsigned_int_option("unwind"),
//                logic,
//                options.get_option("save-summaries"));
        }
        else{
            cbmc_error_interface("Error: invalid request for listing the template; it is supported only in LRA and EUF");
        }
        return false;
    }

    return true;
}

/*******************************************************************\
  
 Function:

 Purpose: 

\*******************************************************************/
void parser_hifrogt::set_options(const cmdlinet &cmdline)
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

//*********** Upgrade Checking options ***********
  options.set_option("init-upgrade-check", cmdline.isset("init-upgrade-check"));
  if (cmdline.isset("do-upgrade-check")) {
    options.set_option("do-upgrade-check", cmdline.get_value("do-upgrade-check"));
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
void parser_hifrogt::eval_verbosity()
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

/*******************************************************************\

 Function: parser_hifrogt::help

 Inputs:

 Outputs:

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
      " hifrog [options] <file>       run on goto-binary `file'\n"
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
      "--no-cex-model                 skips the cex validator is model cannot be extracted \n"
      #ifdef PRODUCE_PROOF
      "\nUpgrade Checking options:\n"
      "--init-upgrade-check           prepare for upgrade checking\n"
      "--do-upgrade-check <filename>  incremental upgrade check with the specified\n"
      "                               upgraded version (goto-binary)\n"
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

 Function: standalone process_goto_program

 Purpose: SA: This standalone function used to be a member function of parse;
 but now inorder to be reusebale for several goto_model we took it out of parser_hifrog class.

 Note: KE: Previously was inspired by: cbmc_parseoptionst::process_goto_program

\*******************************************************************/
bool process_goto_program(const cmdlinet &cmdline, const optionst &options, goto_modelt &goto_model,
                          messaget &msg) {
  try
  {
    // Only to prop logic
    if(cmdline.isset(HiFrogOptions::LOGIC.c_str()))
    {
      if (cmdline.get_value(HiFrogOptions::LOGIC.c_str()) == "prop")  //TODO extend it to other logics as well
      {
        // add the library
        link_to_library(
            goto_model, msg.get_message_handler(), cprover_cpp_library_factory);
        link_to_library(
            goto_model, msg.get_message_handler(), cprover_c_library_factory);
      }
      else
      {
        // use message for printing instead of cbmc_status_interface
//      cbmc_status_interface("Ignoring CPROVER library");
        msg.status() << "Ignoring CPROVER library" << msg.eom;
      }
    }
    else
    {
      msg.status() << "Ignoring CPROVER library" <<  msg.eom;
    }

    if(cmdline.isset("string-abstraction"))
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
    // remove_returns(symbol_table, goto_functions); //KE: causes issues with theoref
    remove_vector(goto_model);
    remove_complex(goto_model);
    rewrite_union(goto_model);

    // add generic checks
    msg.status() << "Generic Property Instrumentation" << msg.eom;
    goto_check(options, goto_model);

    // HIFROG: We remove built-ins from smt logics
    if(cmdline.isset(HiFrogOptions::LOGIC.c_str()))
    {
      if (cmdline.get_value(HiFrogOptions::LOGIC.c_str()) == "prop")
      {
        // checks don't know about adjusted float expressions
        adjust_float_expressions(goto_model);
      }
    }

    if(cmdline.isset("string-abstraction"))
    {
      msg.status() << "String Abstraction" << msg.eom;
      string_abstraction(
          goto_model,
          msg.get_message_handler());
    }

    // add failed symbols
    // needs to be done before pointer analysis
    add_failed_symbols(goto_model.symbol_table);

    // recalculate numbers, etc.
    goto_model.goto_functions.update();

    // add loop ids
    goto_model.goto_functions.compute_loop_numbers();


    // remove skips
    remove_skip(goto_model);
    goto_model.goto_functions.update();

    label_properties(goto_model);
  }

  catch(const char *e)
  {
    msg.error() << e <<msg.eom;
    return true;
  }

  catch(const std::string e)
  {
    msg.error() << e <<msg.eom;
    return true;
  }

  catch(int)
  {
    return true;
  }

  catch(std::bad_alloc)
  {
    msg.error() << "Out of memory" <<msg.eom;
    return true;
  }

  return false;
}
