/*******************************************************************

 Module: Assertion checker that extracts and uses function 
 summaries

 Author: Ondrej Sery

\*******************************************************************/
#include "core_checker.h"

#include "refiner_assertion_sum.h"
#include "solvers/smtcheck_opensmt2_lia.h"
#include "solvers/smtcheck_opensmt2_lra.h"
#include "solvers/smtcheck_opensmt2_cuf.h"
#include "solvers/smtcheck_opensmt2_uf.h"
#include "solvers/satcheck_opensmt2.h"
#include "dependency_checker.h"
#include "nopartition/symex_no_partition.h"
#include "partition_iface.h"
#include "nopartition/smt_assertion_no_partition.h"
#include "partitioning_target_equation.h"
#include "prepare_formula.h"
#include "symex_assertion_sum.h"
#include <funfrog/utils/naming_helpers.h>
#include <funfrog/utils/string_utils.h>
#include "smt_summary_store.h"
#include "prop_summary_store.h"
#include "theory_refiner.h"
#include "partitioning_slice.h"
#include "utils/unsupported_operations.h"

#include <stdio.h>
#include <memory>

namespace{
    /*******************************************************************\

Function: get_refine_mode

  Inputs:

 Outputs:

 Purpose: Determining the refinement mode from a string.

\*******************************************************************/

    refinement_modet get_refine_mode(const std::string& str)
    {
        if (str == "force-inlining" || str == "0"){
            return refinement_modet::FORCE_INLINING;
        } else if (str == "random-substitution" || str == "1"){
            return refinement_modet::RANDOM_SUBSTITUTION;
        } else if (str == "slicing-result" || str == "2"){
            return refinement_modet::SLICING_RESULT;
        } else {
            // by default
            return refinement_modet::SLICING_RESULT;
        }
    }

/*******************************************************************\

Function: get_initial_mode

  Inputs:

 Outputs:

 Purpose: Determining the initial mode from a string.

\*******************************************************************/

    init_modet get_init_mode(const std::string& str)
    {
        if (str == "havoc-all" || str == "0"){
            return init_modet::ALL_HAVOCING;
        } else if (str == "use-summaries" || str == "1"){
            return init_modet::ALL_SUBSTITUTING;
        } else {
            // by default
            return init_modet::ALL_SUBSTITUTING;
        }
    }
}

core_checkert::core_checkert(const goto_modelt & _goto_model, const optionst & _options,
                             ui_message_handlert & _message_handler, unsigned long & _max_memory_used) :
        goto_model{_goto_model},
        ns{goto_model.symbol_table, new_symbol_table},
        options(_options),
        message_handler (_message_handler),
        max_memory_used(_max_memory_used),
        omega(_goto_model.goto_functions, options.get_unsigned_int_option("unwind")),
        summary_store{nullptr}
{
    set_message_handler(_message_handler);
}

core_checkert::~core_checkert(){
    //delete decider;
}

void core_checkert::initialize_solver()
{
    std::string _logic = options.get_option(HiFrogOptions::LOGIC);
    if(_logic == "qfuf") 
    {
        initialize__euf_option_solver();
        decider = initialize__euf_solver(); 
        status() << ("Use QF_UF logic.") << eom;
    }
    else if(_logic == "qfcuf")
    {
        initialize__cuf_option_solver();
        decider = initialize__cuf_solver();
        status() << ("Use QF_CUF logic.") << eom;
    }
    else if(_logic == "qflra") 
    {
        initialize__lra_option_solver();
        decider = initialize__lra_solver();
        status() << ("Use QF_LRA logic.") << eom;
    }
    else if(_logic == "qflia") 
    {
        initialize__lia_option_solver();
        decider = initialize__lia_solver();
        status() << ("Use QF_LIA logic.") << eom;
    }
    else if (_logic == "prop")
    {
        initialize__prop_option_solver();
        decider = initialize__prop_solver();
        status() << ("Use propositional logic.") << eom;
    }
    else 
    {
        error() << ("Unsupported theory: " +  _logic + "\n") << eom;
        exit(0); //Unsupported 
    }
}

// Generic initialise for any solver - euf
void core_checkert::initialize__euf_option_solver()
{
#ifdef PRODUCE_PROOF
    if (is_option_set("itp-uf-algorithm")) 
        solver_options.m_uf_itp_algorithm = options.get_signed_int_option("itp-uf-algorithm");
#endif
        
    initialize_solver_options();
        
    initialize_solver_debug_options();
}
// Generic creation for any solver - euf
smtcheck_opensmt2t_uf * core_checkert::initialize__euf_solver()
{
    return new smtcheck_opensmt2t_uf(solver_options, "uf checker");
}

// Generic initialise for OpenSMT solver - cuf
void core_checkert::initialize__cuf_option_solver()
{
    solver_options.initialize_mix_encoding_solver_options(
            options.get_unsigned_int_option("type-byte-constraints"), 
            options.get_unsigned_int_option("bitwidth"));
    
    //initialize_solver_options(); // TODO: when we have interpolation
    
    initialize_solver_debug_options();
}

// Only for OpenSMT solver - cuf
smtcheck_opensmt2t_cuf * core_checkert::initialize__cuf_solver()
{
    return new smtcheck_opensmt2t_cuf(solver_options, "cuf checker");
}

// Generic initialise for any solver - lra
void core_checkert::initialize__lra_option_solver()
{
    solver_options.initialize_numeric_solver_options(options.get_unsigned_int_option("type-constraints"));
    
    initialize_solver_options();
        
    initialize_solver_debug_options();    
}

// Generic creation for any solver - lra
smtcheck_opensmt2t_lra * core_checkert::initialize__lra_solver()
{
    return new smtcheck_opensmt2t_lra(solver_options, "lra checker");
}

// Generic initialise for any solver - lia
void core_checkert::initialize__lia_option_solver()
{
    solver_options.initialize_numeric_solver_options(options.get_unsigned_int_option("type-constraints"));
    
    //initialize_solver_options(); // TODO: when we have interpolation
        
    initialize_solver_debug_options();    
}

// Generic creation for any solver - lra
smtcheck_opensmt2t_lia * core_checkert::initialize__lia_solver()
{
    return new smtcheck_opensmt2t_lia(solver_options, "lia checker");
}

// Generic initialise for any solver - lia
void core_checkert::initialize__prop_option_solver()
{
    if (is_option_set("itp-algorithm")) 
        solver_options.m_prop_itp_algorithm = options.get_signed_int_option("itp-algorithm");
 
    initialize_solver_options();
        
    initialize_solver_debug_options();    
}

// Only for OpenSMT solver - prop
satcheck_opensmt2t * core_checkert::initialize__prop_solver()
{
    if (options.get_bool_option("no-partitions")) {
        error() << ("--no-partitions option is not supported in theory: " +  options.get_option("logic") + "\n") << eom;
        exit(0); //Unsupported 
    }

    // If all OK, create the decider
    return new satcheck_opensmt2t(solver_options, "prop checker", ns);
}

void core_checkert::initialize_solver_debug_options()
{
#ifdef DISABLE_OPTIMIZATIONS
    solver_options.initialize_solver_debug_options(
    options.get_bool_option("dump-query"),
    options.get_bool_option("dump-pre-query"),
    options.get_option("dump-query-name"));
#endif // DISABLE_OPTIMIZATIONS   
}

void core_checkert::initialize_solver_options()
{
    // Set all the rest of the option - KE: check what to shift to the part of SMT only
    solver_options.m_verbosity = options.get_unsigned_int_option("verbose-solver");
  
    if(options.get_unsigned_int_option("random-seed")) 
        solver_options.m_random_seed = options.get_unsigned_int_option("random-seed");
        
#ifdef PRODUCE_PROOF
    solver_options.m_certify = options.get_unsigned_int_option("check-itp");
    bool do_reduce = options.get_bool_option("reduce-proof");
    if (do_reduce) {
        solver_options.m_do_reduce = true;
        solver_options.m_reduction_loops = options.get_unsigned_int_option("reduce-proof-loops");
        solver_options.m_reduction_graph = options.get_unsigned_int_option("reduce-proof-graph");
    }
#endif 
} 

void core_checkert::initialize()
{
    initialize_solver();
  
    // Init the summary storage
    // Prop and SMT have different mechanism to load/store summaries
    // TODO: unify this mechanism
    if (options.get_option(HiFrogOptions::LOGIC) == "prop")
        summary_store = std::unique_ptr<summary_storet>(new prop_summary_storet());
    else{
        auto smt_decider = dynamic_cast<smtcheck_opensmt2t*>(decider);
        summary_store = std::unique_ptr<summary_storet>(new smt_summary_storet(smt_decider));
    }

    // Load older summaries
    {
        const std::string& filenames = options.get_option("load-summaries");
        std::vector<std::string> summaries_files = splitString(filenames, ',');
        if (!summaries_files.empty()) {
            summary_store->deserialize(summaries_files);
        }
    }

  // Prepare summary_info (encapsulated in omega), start with the lazy variant,
  // i.e., all summaries are initialized as HAVOC, except those on the way
  // to the target assertion, which are marked depending on initial mode.

  omega.initialize_summary_info (omega.get_call_tree_root(), get_main_function());
  //omega.process_goto_locations();
  init = get_init_mode(options.get_option("init-mode"));
  omega.setup_default_precision(init);
}

void get_ints(std::vector<unsigned>& claims, std::string set){

  unsigned int length=set.length();

  for(unsigned idx=0; idx<length; idx++)
  {
    std::string::size_type next=set.find(",", idx);
    std::string val=set.substr(idx, next-idx);
    claims.push_back(atoi(val.c_str()));

    if(next==std::string::npos) break;
    idx=next;
  }
}

/*******************************************************************

 Function: core_checkert::assertion_holds

 Inputs:

 Outputs:

 Purpose: Checks if the given assertion of the GP holds

\*******************************************************************/

bool core_checkert::assertion_holds(const assertion_infot& assertion,
        bool store_summaries_with_assertion)
{
  // Trivial case
  if(assertion.is_trivially_true())
  {
    status() << ("Assertion(s) hold trivially.") << eom;
    report_success();
    
#ifdef PRODUCE_PROOF      
    if (assertion.is_single_assert()) // If Any or Multi cannot use get_location()
        status() << ((assertion.is_assert_grouping()) 
                ? "\n\nMain Checked Assertion: " : "\n\nChecked Assertion: ") <<
            "\n  file " << assertion.get_location()->source_location.get_file() <<
            " line " << assertion.get_location()->source_location.get_line() <<
            " function " << assertion.get_location()->source_location.get_function() << 
            "\n  " << ((assertion.get_location()->is_assert()) ? "assertion" : "code") <<
            "\n  " << from_expr(assertion.get_location()->guard)
            << eom;
#endif
    
    return true;
  }
  
  if (options.get_bool_option("no-partitions")) // BMC alike version
    return assertion_holds_smt_no_partition(assertion);
  else
    return assertion_holds_(assertion, store_summaries_with_assertion);
}

/*******************************************************************

 Function: core_checkert::assertion_holds_

 Inputs:

 Outputs:

 Purpose: Checks if the given assertion of the GP holds for smt encoding

\*******************************************************************/

bool core_checkert::assertion_holds_(const assertion_infot & assertion,
                                     bool store_summaries_with_assertion)
{
    absolute_timet initial, final;
    initial = current_time();
 
    // Init the objects:
    const bool no_ce_option = options.get_bool_option(HiFrogOptions::NO_ERROR_TRACE);
    const unsigned int unwind_bound = options.get_unsigned_int_option(HiFrogOptions::UNWIND);

    // prepare omega
    const auto & const_summary_store = *summary_store;
    auto has_summary = [&const_summary_store](const std::string & function_name){
        return const_summary_store.has_summaries(function_name);
    };
    omega.set_initial_precision(assertion, has_summary);
    const unsigned last_assertion_loc = omega.get_last_assertion_loc();
    const bool single_assertion_check = omega.is_single_assertion_check();

    partitioning_target_equationt equation(ns, *summary_store,
                                                store_summaries_with_assertion);

#ifdef DISABLE_OPTIMIZATIONS
    if (options.get_bool_option("dump-SSA-tree")) {
        equation.set_dump_SSA_tree(true);
        equation.set_dump_SSA_tree_name(options.get_option("dump-query-name"));
    }
#endif
  
    call_tree_nodet& call_tree_root = omega.get_call_tree_root();
    symex_assertion_sumt symex = symex_assertion_sumt(get_goto_functions(), call_tree_root, ns, new_symbol_table,
                                                      equation,
                                                      message_handler, get_main_function(), last_assertion_loc,
                                                      single_assertion_check, !no_ce_option,
                                                      unwind_bound,
                                                      options.get_bool_option("partial-loops"));
    symex.set_assertion_info_to_verify(&assertion);

    refiner_assertion_sumt refiner {
              *summary_store, omega,
              get_refine_mode(options.get_option("refine-mode")),
              message_handler, last_assertion_loc};

    bool end = prepareSSA(symex);
    if(!end && options.get_bool_option("claims-opt")){
        dependency_checkert(ns,
                    message_handler, 
                    get_main_function(),
                    omega, 
                    options.get_unsigned_int_option("claims-opt"), 
                    equation.SSA_steps.size())
                .do_it(equation);
        status() << (std::string("Ignored SSA steps after dependency checker: ") + std::to_string(equation.count_ignored_SSA_steps())) << eom;
    }


    // the checker main loop:
    unsigned summaries_used = 0;
    unsigned iteration_counter = 0;
    prepare_formulat ssaToFormula = prepare_formulat(equation, message_handler);
    while (!end) {
        iteration_counter++;

        //Converts SSA to SMT formula
        ssaToFormula.convert_to_formula( *decider, *(decider));

        // Decides the equation
        bool is_sat = ssaToFormula.is_satisfiable(*decider);
        summaries_used = omega.get_summaries_count();
        
        end = !is_sat;
        if (is_sat) {
            // this refiner can refine if we have summary or havoc representation of a function
            // Else quit the loop! (shall move into a function)
            if (omega.get_summaries_count() == 0 && omega.get_nondets_count() == 0) 
                // nothing left to refine, cex is real -> break out of the refinement loop
                break;
            
            // Else, report and try to refine!
            
            // REPORT part
            if (summaries_used > 0){
                status() << "FUNCTION SUMMARIES (for " << summaries_used << " calls) AREN'T SUITABLE FOR CHECKING ASSERTION." << eom;
            }

            const unsigned int nondet_used = omega.get_nondets_count();
            if (nondet_used > 0){
                status() << "HAVOCING (of " << nondet_used << " calls) AREN'T SUITABLE FOR CHECKING ASSERTION." << eom;
            }
            // END of REPORT

            // figure out functions that can be refined
            refiner.mark_sum_for_refine(*decider, omega.get_call_tree_root(), equation);
            bool refined = !refiner.get_refined_functions().empty();
            if (!refined) {
                // nothing could be refined to rule out the cex, it is real -> break out of refinement loop
                break;
            } else {
                // REPORT
                status() << ("Go to next iteration\n") << eom;
                // do the actual refinement of ssa
                refineSSA(symex, refiner.get_refined_functions());
            }
        }
    } // end of refinement loop
  
  
    ////////////////// 
    // Report Part: //
    //////////////////
  
    // the assertion has been successfully verified if we have (end == true)
    const bool is_verified = end;
    if (is_verified) {
        // produce and store the summaries   
        if (!options.get_bool_option("no-itp")) {
            #ifdef PRODUCE_PROOF
            if (decider->can_interpolate()) {
                status() << ("Start generating interpolants...") << eom;
                extract_interpolants(equation);
            } else {
                status() << ("Skip generating interpolants") << eom;
            }
            #else
                assert(0); // Cannot produce proof in that case!
            #endif

        } else {
            status() << ("Skip generating interpolants") << eom;
        } // End Report interpolation gen.
    
        // Report Summaries use
        if (summaries_used > 0)
        {
            status() << "FUNCTION SUMMARIES (for " << summaries_used
                     << " calls) WERE SUBSTITUTED SUCCESSFULLY." << eom;
        } else {
            status() << ("ASSERTION(S) HOLD(S) WITH FULL INLINE") << eom;
        }

        // report results
        report_success();
        
    } // End of UNSAT section
    else // assertion was falsified
    {
        assertion_violated(ssaToFormula, symex.guard_expln);
    }
    // FINAL REPORT

    final = current_time();
    omega.get_unwinding_depth();

    status() << "Initial unwinding bound: " << options.get_unsigned_int_option("unwind") << eom;
    status() << "Total number of steps: " << iteration_counter << eom;
    if (omega.get_recursive_total() > 0){
        status() << "Unwinding depth: " <<  omega.get_recursive_max() << " (" << omega.get_recursive_total() << ")" << eom;
    }
    status() << "TOTAL TIME FOR CHECKING THIS CLAIM: " << (final - initial) << eom;
 
#ifdef PRODUCE_PROOF  
    if (assertion.is_single_assert()) // If Any or Multi cannot use get_location())
        status() << ((assertion.is_assert_grouping()) 
                ? "\n\nMain Checked Assertion: " : "\n\nChecked Assertion: ") <<
              "\n  file " << assertion.get_location()->source_location.get_file() <<
              " line " << assertion.get_location()->source_location.get_line() <<
              " function " << assertion.get_location()->source_location.get_function() << 
              "\n  " << ((assertion.get_location()->is_assert()) ? "assertion" : "code") <<
              "\n  " << from_expr(ns, "", assertion.get_location()->guard)  
              << eom;  
#endif
  
  return is_verified;
}

/*******************************************************************

 Function: core_checkert::assertion_holds_smt_no_partition

 Inputs:

 Outputs:

 Purpose: Checks if the given assertion of the GP holds for smt encoding

\*******************************************************************/

bool core_checkert::assertion_holds_smt_no_partition(
        const assertion_infot& assertion)
{
  absolute_timet initial, final;
  initial=current_time();
  
  const bool no_slicing_option = options.get_bool_option(HiFrogOptions::NO_SLICING);
//  const bool no_ce_option = options.get_bool_option("no-error-trace");

    const auto & const_summary_store = *summary_store;
    auto has_summary = [&const_summary_store](const std::string & function_name){
        return const_summary_store.has_summaries(function_name);
    };
  omega.set_initial_precision(assertion, has_summary);
//  const unsigned last_assertion_loc = omega.get_last_assertion_loc();
//  const bool single_assertion_check = omega.is_single_assertion_check();

  hifrog_symex_target_equationt equation(ns);
#ifdef DISABLE_OPTIMIZATIONS
  if (options.get_bool_option("dump-SSA-tree")) {
    equation.set_dump_SSA_tree(true);
    equation.set_dump_SSA_tree_name(options.get_option("dump-query-name"));
  }
#endif
  
  symex_no_partitiont symex = symex_no_partitiont(ns, new_symbol_table, equation, message_handler, get_main_function(),!no_slicing_option);
  symex.setup_unwind(options.get_unsigned_int_option(HiFrogOptions::UNWIND));


  smt_assertion_no_partitiont prop = smt_assertion_no_partitiont(
          equation, message_handler, max_memory_used);
  
  unsigned count = 0;
  bool end = false;
  std::cout <<"";

  
  while (!end)
  {
    count++;
    end = (count == 1) 
            ? symex.prepare_SSA(assertion, omega.get_goto_functions())
            : symex.refine_SSA (assertion, false); // Missing sets of refined functions, TODO

    //LA: good place?
//    if(options.get_bool_option("list-templates"))
//    {
//        status() << "No listing templates option in this mode\n" << eom;
//        return true;
//    }

    if (!end){
      if (options.get_bool_option("claims-opt") && count == 1){
        dependency_checkert(ns, message_handler, get_main_function(), omega, options.get_unsigned_int_option("claims-opt"), equation.SSA_steps.size())
                .do_it(equation);
        status() << (std::string("Ignored SSA steps after dependency checker: ") + std::to_string(equation.count_ignored_SSA_steps())) << eom;
      }

      end = prop.assertion_holds( 
              *(dynamic_cast<smtcheck_opensmt2t *> (decider)));
      unsigned summaries_count = omega.get_summaries_count();
      // MB: unused variable commented out
      //unsigned nondet_count = omega.get_nondets_count();
      if (end)
      {
        if (options.get_bool_option("no-itp"))
          status() << ("Skip generating interpolants") << eom;

        if (summaries_count == 0)
        {
          status() << ("ASSERTION(S) HOLD(S) ") << eom; //TODO change the message to something more clear (like, everything was inlined...)
        } else {
          status() << "FUNCTION SUMMARIES (for " << summaries_count
        	   << " calls) WERE SUBSTITUTED SUCCESSFULLY." << eom;
        }
        report_success();
      } else {
          // TOOD - take care of the basic (old) refinement
        /*if (summaries_count > 0 || nondet_count > 0) {
          if (summaries_count > 0){
            status() << "FUNCTION SUMMARIES (for " << summaries_count
                   << " calls) AREN'T SUITABLE FOR CHECKING ASSERTION." << eom;
          }
          if (nondet_count > 0){
            status() << "HAVOCING (of " << nondet_count
                   << " calls) AREN'T SUITABLE FOR CHECKING ASSERTION." << eom;
          }
          refiner.refine(*(dynamic_cast <smtcheck_opensmt2t*> (decider)), omega.get_call_tree_root(), equation);

          if (refiner.get_refined_functions().size() == 0){
            assertion_violated(prop, symex.guard_expln);
            break;
          } else {
            //status("Counterexample is spurious");
            status() << ("Go to next iteration\n") << eom;
          }
        } else {*/
          assertion_violated(prop, symex.guard_expln);
          break;
        //}
      }
    }
  }
  final = current_time();
  omega.get_unwinding_depth();

  status() << "Initial unwinding bound: " << options.get_unsigned_int_option("unwind") << eom;
  status() << "Total number of steps: " << count << eom;
  if (omega.get_recursive_total() > 0){
    status() << "Unwinding depth: " <<  omega.get_recursive_max() << " (" << omega.get_recursive_total() << ")" << eom;
  }
  status() << "TOTAL TIME FOR CHECKING THIS CLAIM: " << (final - initial) << eom;
 
#ifdef PRODUCE_PROOF 
    if (assertion.is_single_assert()) // If Any or Multi cannot use get_location())
        status() << ((assertion.is_assert_grouping()) 
                ? "\n\nMain Checked Assertion: " : "\n\nChecked Assertion: ") <<
              "\n  file " << assertion.get_location()->source_location.get_file() <<
              " line " << assertion.get_location()->source_location.get_line() <<
              " function " << assertion.get_location()->source_location.get_function() << 
              "\n  " << ((assertion.get_location()->is_assert()) ? "assertion" : "code") <<
              "\n  " << from_expr(ns, "", assertion.get_location()->guard)  
              << eom;  
#endif
  
  return end;
}

  
/*******************************************************************

 Function: core_checkert::assertion_violated

 Inputs:

 Outputs:

 Purpose: Prints the error trace for smt encoding

\*******************************************************************/
void core_checkert::assertion_violated (prepare_formulat& prop,
				std::map<irep_idt, std::string> &guard_expln)
{
    if (!options.get_bool_option("no-error-trace"))
        prop.error_trace(*decider, ns, guard_expln);
    if (decider->is_overapprox_encoding()){
    	status() << "\nA bug found." << eom;
    	status() << "WARNING: Possibly due to the Theory conversion." << eom;
    } else {
    	status() << "A real bug found." << eom;
    }
    report_failure();
}

/*******************************************************************

 Function: core_checkert::assertion_violated

 Inputs:

 Outputs:

 Purpose: Prints the error trace for smt encoding

\*******************************************************************/
void core_checkert::assertion_violated (smt_assertion_no_partitiont& prop,
				std::map<irep_idt, std::string> &guard_expln)
{
    smtcheck_opensmt2t* decider_smt = dynamic_cast <smtcheck_opensmt2t*> (decider);
    if (!options.get_bool_option("no-error-trace"))
        prop.error_trace(*decider_smt, ns, guard_expln);
    if (decider_smt->is_overapprox_encoding()){
    	status() << "\nA bug found." << endl;
    	status() << "WARNING: Possibly due to the Theory conversion." << eom;
    } else {
    	status() << "A real bug found." << eom;
    }
    report_failure();

    decider_smt = nullptr;
}

#ifdef PRODUCE_PROOF
/*******************************************************************\

Function: core_checkert::extract_interpolants_smt

  Inputs:

 Outputs:

 Purpose: Extract and store the interpolation summaries for smt only

\*******************************************************************/
void core_checkert::extract_interpolants (partitioning_target_equationt& equation)
{
  absolute_timet before, after;
  before=current_time();
  
  equation.extract_interpolants(*decider);

  after=current_time();
  status() << "INTERPOLATION TIME: " << (after-before) << eom;
  
  // Store the summaries
  const std::string& summary_file = options.get_option("save-summaries");
  if (!summary_file.empty()) {
    std::ofstream out;
    out.open(summary_file.c_str());
    summary_store->serialize(out);
  }
}
#endif

/*******************************************************************\

Function: core_checkert::report_success

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void core_checkert::report_success()
{
  //result() << ("VERIFICATION SUCCESSFUL");

  switch(message_handler.get_ui())
  {
  
    case ui_message_handlert::uit::PLAIN:
	result() << "\nVERIFICATION SUCCESSFUL" << eom;
	break;

    case ui_message_handlert::uit::XML_UI:
    {
      xmlt xml("cprover-status");
      xml.data="SUCCESS";
      std::cout << xml;
      std::cout << std::endl;
    }
    break;

  default:
    assert(false);
  }
}

/*******************************************************************\

Function: core_checkert::report_failure

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void core_checkert::report_failure()
{
  switch(message_handler.get_ui())
  {

    case ui_message_handlert::uit::PLAIN:
	result() << "\nVERIFICATION FAILED" << eom;;
	break;

    case ui_message_handlert::uit::XML_UI:
    {
      xmlt xml("cprover-status");
      xml.data="FAILURE";
      std::cout << xml;
      std::cout << std::endl;
    }
    break;

  default:
    assert(false);
  }
}

/*******************************************************************\

Function: core_checkert::report_failure

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/
#ifdef PRODUCE_PROOF
namespace{
//Purpose: extracts summaries after successful verification; and dumps the summaries
// in a specific summary-file for uf and lra separately based on the solver.

    void extract_and_store_summaries(partitioning_target_equationt & equation, summary_storet & store,
                                      smtcheck_opensmt2t & decider , std::string & summary_file_name){
        equation.extract_interpolants(decider);

        // Store the summaries
        if (!summary_file_name.empty()) {
            std::ofstream out;
            out.open(summary_file_name.c_str());
            //dumps define-fun()  into summary file
            out << decider.getSimpleHeader();
            store.serialize(out);
            out.close();
        }

    }

/*******************************************************************/
// Purpose:
void reload_summaries(const namespacet &ns,
                      smt_summary_storet & store, std::vector<std::string> const & filenames,
                      smtcheck_opensmt2t_lra & decider, smtcheck_opensmt2t_uf & prev_solver) {

    // Put the whole summary file in string
    std::stringstream dump;
    dump << decider.getSimpleHeader();  // gets all the declarations without the variables
    store.serialize(dump);
    std::string sm = dump.str();

    // Detect unsupported functions
    std::vector<std::string> unsupp_func = get_unsupported_funct_exprs(sm);

    // Detect if there are non-linear parts (searching for non-linear / or *):
    std::set<PTRef> non_linears = prev_solver.get_non_linears();
    if (non_linears.size() > 0 || !unsupp_func.empty())
    {
        const Logic& logic = *prev_solver.getLogic();
        std::transform(non_linears.begin(), non_linears.end(), std::back_inserter(unsupp_func),
                       [&logic](PTRef pt){ return std::string{logic.printTerm(pt)};});
        // Notify the user
        std::cerr << "Non linear operation encounter. Ignoring " << non_linears.size() << " expressions in the file.\n";

        std::sort(unsupp_func.begin(), unsupp_func.end(), [](const std::string & first, const std::string & second){
            return first.size() > second.size();
        });

        // Replace all non-linear expressions in unsupported variable
        for(auto old_token : unsupp_func)
        {
            // Get the old token we wish to abstract
            std::string new_token = fresh_var_name_nonlinear();
            prev_solver.getLogic()->mkVar(prev_solver.getURealSortRef(), new_token.c_str());
            // New Unsupported Var with no specific mapping or information saved
            
            // The symbol name in the old token
            std::string::size_type n_before = 0;
            std::string::size_type n_after = 0;
            while ( ( n_before = old_token.find( "|", n_after) ) != std::string::npos )
            {
                if (( n_after = old_token.find( "|", n_before+1) ) != std::string::npos)
                {
                    // Get SSA names in the old token
                    std::string id_str_SSA = old_token.substr( n_before+1, n_after-n_before-1);
                    std::string id_str_curr = id_str_SSA;
                    irep_idt identifier = id_str_curr;

                    // Get the symbol name of the SSA name:
                    const symbolt *symbol =0;
                    while (ns.lookup(identifier, symbol) && id_str_curr.size()>0)
                    {
                        id_str_curr = id_str_curr.substr(0,id_str_curr.size()-1);
                        identifier = id_str_curr;
                    }
//                        std::cout << "** Replace : " << id_str_SSA << " in " << id_str_curr << std::endl;

                    // Fix the old token to use symbols and not SSAs
                    old_token.replace( n_before+1, id_str_SSA.size(), id_str_curr );
                    n_before = old_token.find(id_str_curr, n_before) + id_str_curr.size()+1;
                    n_after = n_before;
                } else {
                    break;
                }
            }

            // Create the abstract summary:
            std::string::size_type n = 0;
            while ( ( n = sm.find( old_token, n ) ) != std::string::npos )
            {
                sm.replace( n, old_token.size(), new_token );
                n += new_token.size();
            }
//              std::cout << "Replacing " << old_token << " in " << new_token << std::endl;
        }

        // Store to Temp. file
        std::ofstream out;
        out.open("__summaries_linear_temp");
        //dumps define-fun()  into summary file
        out << prev_solver.getSimpleHeader() << sm;
        out.close();

        std::vector<std::string> filenames_linear;
        for(auto const & filename : filenames){   //takes care of the cases that uf-file has only mod as a non-linear exp
            if(filename != "__summaries_uf"){
                filenames_linear.push_back(filename);
            }
        }
//            filenames_linear.insert(filenames_linear.begin(), filenames.begin(), filenames.end());
        filenames_linear.push_back(std::string("__summaries_linear_temp"));

        // Final stage:
        store.set_decider(&decider);
        store.deserialize(filenames_linear);

        // Remove the temp. file
        remove( "__summaries_linear_temp" );
    } else {
        // Final stage:
        store.set_decider(&decider);
        store.deserialize(filenames);
    }
}

/*******************************************************************/
// Purpose: reset means changing the partition information according
// to the current state of the summary store. so first we updated the
// store using method read_lra_summaries(), then we update the summary information
    void reset_partition_info(partitioning_target_equationt & eq, smt_summary_storet const & store) {
        for (auto & partition : eq.get_partitions()){
            partition.event_solver_reseted();
            // check if we have summary in the store for this partition
            const auto & function_name = id2string(partition.get_iface().function_id);
            bool should_summarize = partition.get_iface().call_tree_node.get_precision() == summary_precisiont::SUMMARY;
            // should_summarize -> store.has_summaries
            assert(!should_summarize || store.has_summaries(function_name));
            bool was_summarized = partition.has_summary_representation();
            if(should_summarize){
                // clear the old information and load new information from the store
                // fill the partition with new summaries
                eq.fill_summary_partition(partition.get_iface().partition_id, function_name);
                assert(partition.has_summary_representation());
            }
            else{
                if(was_summarized){
                    // if it was summarized before but we do not have summaries now, that indicates an error, because we do not want to do symex again,
                    // we assume that everything that has summaries before, has summaries again
                    throw std::logic_error("During refinement we lost summaries for " + function_name);

                }
            }
        }
    }
}
#endif // PRODUCE_PROOF
/*******************************************************************\

Function: core_checkert::check_sum_theoref_single

  Inputs:

 Outputs:

 Purpose: main method to make summary-ref and theory-ref work together

\*******************************************************************/
#ifdef PRODUCE_PROOF
bool core_checkert::check_sum_theoref_single(const assertion_infot &assertion)
{
    new_symbol_table.clear(); // MB: this needs to be empty before use in symex
    std::string lra_summary_file_name {"__summaries_lra"};
    std::string uf_summary_file_name {"__summaries_uf"};
    initialize__euf_option_solver();
    auto uf_solver_ptr = std::unique_ptr<smtcheck_opensmt2t_uf>{initialize__euf_solver()};
    auto & uf_solver = *uf_solver_ptr;


    smt_summary_storet summary_store {uf_solver_ptr.get()};
    //reading summary by uf
    status() << "\n--Reading UF summary file: " << uf_summary_file_name << eom;
    summary_store.deserialize({uf_summary_file_name});
    const auto & const_summary_store = summary_store;
    auto has_summary = [&const_summary_store]
            (const std::string & function_name){
        return const_summary_store.has_summaries(function_name);
    };
    omega.set_initial_precision(assertion, has_summary);
    partitioning_target_equationt equation {ns, summary_store, false};

    symex_assertion_sumt symex{get_goto_functions(),
                               omega.get_call_tree_root(),
                               ns,
                               new_symbol_table,
                               equation,
                               message_handler,
                               get_main_function(),
                               omega.get_last_assertion_loc(),
                               omega.is_single_assertion_check(),
                               !options.get_bool_option("no-error-trace"),
                               options.get_unsigned_int_option("unwind"),
                               options.get_bool_option("partial-loops"),
    };
    symex.set_assertion_info_to_verify(&assertion);

    bool assertion_holds = prepareSSA(symex);
    if (assertion_holds){
        // report results
        report_success();
        // Claim trivially satisfied -> go to next claim
        status() << ("This assertion trivially holds, Go to next claim ...\n") << eom;
        return true;
    }

    equation.convert(uf_solver, uf_solver);
    bool is_sat = uf_solver.solve();
    if (!is_sat) {
        // interpolate if possible
        extract_and_store_summaries(equation, summary_store, uf_solver , uf_summary_file_name);
        // report results
        report_success();
        status() << ("---Go to next assertion; Claim verified by EUF---\n") << eom;
        return true; // claim verified -> go to next claim
    }
//---------------------------------------------------------------------------
    //UF summary refinement
    status() << "\n---trying to locally refine the summary in UF---\n" <<eom;
    refiner_assertion_sumt localRefine{summary_store, omega,
                                           refinement_modet::SLICING_RESULT,
                                           this->get_message_handler(),
                                           omega.get_last_assertion_loc()};


    localRefine.mark_sum_for_refine(uf_solver, omega.get_call_tree_root(), equation);
    bool can_refine = !localRefine.get_refined_functions().empty();
    while(can_refine) {
        refineSSA(symex, localRefine.get_refined_functions());
        equation.convert(uf_solver, uf_solver);
        is_sat = uf_solver.solve();
        if (!is_sat) {
            extract_and_store_summaries(equation, summary_store, uf_solver, uf_summary_file_name);
            // report results
            report_success();
            status() << ("\n---Go to next assertion; claim verified by UF with some local Refinement---\n") << eom;
            return true; //->Uf was enough, go to next claim
        }
        localRefine.mark_sum_for_refine(uf_solver, omega.get_call_tree_root(), equation);
        can_refine = !localRefine.get_refined_functions().empty();
    }
//---------------------------------------------------------------------------
    status() << "\n---EUF was not enough, lets change the encoding to LRA---\n" <<eom;
    initialize__lra_option_solver();
    auto lra_solver_ptr = std::unique_ptr<smtcheck_opensmt2t_lra>{initialize__lra_solver()};
    auto & lra_solver = *lra_solver_ptr;
    status() << "\n--Reading LRA and UF summary files: " << uf_summary_file_name << "," << lra_summary_file_name << eom;
    reload_summaries(ns, summary_store, {uf_summary_file_name, lra_summary_file_name}, lra_solver, uf_solver );
    omega.set_initial_precision(assertion, has_summary);
    reset_partition_info(equation, summary_store);
    equation.convert(lra_solver, lra_solver);
    is_sat = lra_solver.solve();
    if(!is_sat){
        extract_and_store_summaries(equation, summary_store, lra_solver, lra_summary_file_name);
        // cannot update UF summaries
        // report results
        report_success();
        status() << ("---Go to next assertion; Claim verified by LRA without any local refinement---\n") << eom;
        return true; // claim verified by LRA encoding -> go to next claim
    }
//---------------------------------------------------------------------------
    status() << "\n---trying to locally refine the summary in LRA---\n" << eom;
    // SA: I guess we can use previously generated object localRefine in UF refinement phase
    localRefine.mark_sum_for_refine(lra_solver, omega.get_call_tree_root(), equation);
    can_refine = !localRefine.get_refined_functions().empty();
    while(can_refine){
        refineSSA(symex,localRefine.get_refined_functions());
        equation.convert(lra_solver, lra_solver);
        is_sat = lra_solver.solve();
        if(!is_sat){
            extract_and_store_summaries(equation, summary_store, lra_solver, lra_summary_file_name);
            // report results
            report_success();
            status() << ("\n---Go to next assertion; claim verified by LRA with some local Refinement---\n") << eom;
            return true; // claim verified by LRA encoding -> go to next claim
        }
        localRefine.mark_sum_for_refine(lra_solver, omega.get_call_tree_root(), equation);
        can_refine = !localRefine.get_refined_functions().empty();
    }
    //cal prop --------------------------------------------------------------------------
    status() << "\n---EUF and LRA were not enough; trying to use prop logic ---\n" <<eom;
    std::string prop_summary_filename {"__summaries_prop"};

    this->summary_store.reset(new prop_summary_storet());
    std::ifstream f(prop_summary_filename.c_str());
    if (f.good()) {
        status() << "\n--Reading Prop summary file: " << prop_summary_filename <<"\n" << eom;
        this->summary_store->deserialize(std::vector<std::string>{prop_summary_filename});
    }
    // MB: workaround around assertion_holds_ expecting to have a decider set already
    delete decider;
    initialize__prop_option_solver();
    decider = initialize__prop_solver();
    new_symbol_table.clear();
    auto res = this->assertion_holds_(assertion, false);
    if (res) {
        status() << ("\n---Go to next assertion; claim verified by PROP---\n") << eom;
    }
    return res;
}

#endif // PRODUCE_PROOF

void core_checkert::slice_target(partitioning_target_equationt & equation) {
    auto before = current_time();
    statistics() << "All SSA steps: " << equation.SSA_steps.size() << eom;
    partitioning_slice(equation);
    statistics() << "Ignored SSA steps after slice: " << equation.count_ignored_SSA_steps() << eom;
    auto after = current_time();
    statistics() << "SLICER TIME: " << (after - before) << eom;
}

bool core_checkert::prepareSSA(symex_assertion_sumt & symex) {
    auto verified = symex.prepare_SSA();
    if(!verified && !options.get_bool_option(HiFrogOptions::NO_SLICING)){
        slice_target(symex.get_target_equation());
    }
    return verified;
}

bool core_checkert::refineSSA(symex_assertion_sumt & symex, const std::list<call_tree_nodet *> & functions_to_refine) {
    auto verified = symex.refine_SSA(functions_to_refine);
    if(!verified && !options.get_bool_option(HiFrogOptions::NO_SLICING)){
        slice_target(symex.get_target_equation());
    }
    return verified;
}
