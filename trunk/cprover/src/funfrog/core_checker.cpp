/*******************************************************************

 Module: Assertion checker that extracts and uses function 
 summaries

 Author: Ondrej Sery

\*******************************************************************/
#include "core_checker.h"
#include "dependency_checker.h"

#include "solvers/smtcheck_opensmt2_lra.h"
#include "solvers/smtcheck_opensmt2_cuf.h"
#include "solvers/smtcheck_opensmt2_uf.h"
#include "solvers/satcheck_opensmt2.h"
#include "smt_refiner_assertion_sum.h"
#include "prop_refiner_assertion_sum.h"
#include "smt_dependency_checker.h"
#include "prop_dependency_checker.h"
#include "nopartition/symex_no_partition.h"
#include "partition_iface.h"
#include "nopartition/smt_assertion_no_partition.h"
#include "prop_partitioning_target_equation.h"
#include "smt_partitioning_target_equation.h"
#include "prop_assertion_sum.h"
#include "prepare_smt_formula.h"
#include "symex_assertion_sum.h"
#include <solvers/flattening/bv_pointers.h>
#include "smt_summary_store.h"
#include "prop_summary_store.h"
#include "theory_refiner.h"
#include <stdio.h>

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

core_checkert::core_checkert(
        const goto_programt &_goto_program,
        const goto_functionst &_goto_functions,
        const symbol_tablet &_symbol_table,
        const optionst& _options,
        ui_message_handlert &_message_handler,
        unsigned long &_max_memory_used
) :
        goto_program(_goto_program),
        symbol_table(_symbol_table),
        options(_options),
        message_handler (_message_handler),
        max_memory_used(_max_memory_used),
        omega(_goto_functions, options.get_unsigned_int_option("unwind")),
        summary_store{nullptr}
{
    set_message_handler(_message_handler);
}

core_checkert::~core_checkert(){
    //delete decider;
}

void core_checkert::initialize_solver()
{
    string _logic = options.get_option("logic");
    if(_logic == "qfuf") 
    {
        decider = new smtcheck_opensmt2t_uf("uf checker");
        status() << ("Use QF_UF logic.") << eom;
    }
    else if(_logic == "qfcuf")
    {
        decider = new smtcheck_opensmt2t_cuf(options.get_unsigned_int_option("bitwidth"), 
                options.get_unsigned_int_option("type-byte-constraints"), "cuf checker");
        status() << ("Use QF_CUF logic.") << eom;
    }
    else if(_logic == "qflra") 
    {
        decider = new smtcheck_opensmt2t_lra(options.get_unsigned_int_option("type-constraints"), "lra checker");
        status() << ("Use QF_LRA logic.") << eom;
    }
    else if (_logic == "prop" && !options.get_bool_option("no-partitions"))
    {
        decider = new satcheck_opensmt2t("prop checker");
        status() << ("Use propositional logic.") << eom;
    }
    else if (_logic == "prop" && options.get_bool_option("no-partitions"))
    {
        error() << ("--no-partitions option is not supported in theory: " +  _logic + "\n") << eom;
        exit(0); //Unsupported 
    }
    else 
    {
        error() << ("Unsupported theory: " +  _logic + "\n") << eom;
        exit(0); //Unsupported 
    }
 
    initialize_solver_options(decider); // Init all options in the solver
}

void core_checkert::initialize_solver_options(check_opensmt2t* _decider)
{
  // Set all the rest of the option - KE: check what to shift to the part of SMT only

  _decider->set_verbosity(options.get_unsigned_int_option("verbose-solver"));
#ifdef PRODUCE_PROOF   
  _decider->set_itp_bool_alg(options.get_unsigned_int_option("itp-algorithm"));
  _decider->set_itp_euf_alg(options.get_unsigned_int_option("itp-uf-algorithm"));
  _decider->set_itp_lra_alg(options.get_unsigned_int_option("itp-lra-algorithm"));
  if(options.get_option("itp-lra-factor").size() > 0) 
      _decider->set_itp_lra_factor(options.get_option("itp-lra-factor").c_str());
  _decider->set_certify(options.get_unsigned_int_option("check-itp"));
  if(options.get_bool_option("reduce-proof"))
  {
    _decider->set_reduce_proof(options.get_bool_option("reduce-proof"));
    if(options.get_unsigned_int_option("reduce-proof-graph")) _decider->set_reduce_proof_graph(options.get_unsigned_int_option("reduce-proof-graph"));
    if(options.get_unsigned_int_option("reduce-proof-loops")) _decider->set_reduce_proof_loops(options.get_unsigned_int_option("reduce-proof-loops"));
  }
#endif
  if(options.get_unsigned_int_option("random-seed")) _decider->set_random_seed(options.get_unsigned_int_option("random-seed"));
#ifdef DISABLE_OPTIMIZATIONS  
  if (options.get_bool_option("dump-query"))
      _decider->set_dump_query(true);
  if (options.get_bool_option("dump-pre-query"))
      _decider->set_dump_pre_query(true);
  _decider->set_dump_query_name(options.get_option("dump-query-name"));
#endif  
}

void core_checkert::initialize()
{
    initialize_solver();
  
    // Init the summary storage
    // Prop and SMT have different mechanism to load/store summaries
    // TODO: unify this mechanism
    if (options.get_option("logic") == "prop")
        summary_store = std::unique_ptr<summary_storet>(new prop_summary_storet());
    else{
        auto smt_decider = dynamic_cast<smtcheck_opensmt2t*>(decider);
        summary_store = std::unique_ptr<summary_storet>(new smt_summary_storet(smt_decider));
    }

    // Load older summaries
    {
        //TODO: MB: How about checking if this file actually exists?
        const std::string& summary_file = options.get_option("load-summaries");
        if (!summary_file.empty()) {
            ifstream f(summary_file.c_str());
            if (f.good()) {
                summary_store->deserialize({summary_file});
            }

        }
    }

  // Prepare summary_info (encapsulated in omega), start with the lazy variant,
  // i.e., all summaries are initialized as HAVOC, except those on the way
  // to the target assertion, which are marked depending on initial mode.

  omega.initialize_summary_info (omega.get_call_tree_root(), goto_program);
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
  
  // TODO: need to split this class and create a version for prop and smt
  // Unless we wish to unify mechanism also for error_trace!
  if (options.get_option("logic") == "prop")
    return assertion_holds_prop(assertion, store_summaries_with_assertion);
  else if (options.get_bool_option("no-partitions")) // BMC alike version
    return assertion_holds_smt_no_partition(assertion);
  else 
    return assertion_holds_smt(assertion, store_summaries_with_assertion);
}

/*******************************************************************

 Function: core_checkert::assertion_holds

 Inputs:

 Outputs:

 Purpose: Checks if the given assertion of the GP holds for prop logic

\*******************************************************************/

bool core_checkert::assertion_holds_prop(const assertion_infot& assertion,
        bool store_summaries_with_assertion)
{
  absolute_timet initial, final;
  initial=current_time();
  
  const bool no_slicing_option = options.get_bool_option("no-slicing");
  const bool no_ce_option = options.get_bool_option("no-error-trace");
//  assert(options.get_option("logic") == "prop");
  const unsigned int unwind_bound = options.get_unsigned_int_option("unwind");
  const bool partial_loops = options.get_bool_option("partial-loops");

  const auto & const_summary_store = *summary_store;
  auto has_summary = [&const_summary_store](const std::string & function_name){
      return const_summary_store.has_summaries(function_name);
  };
  omega.set_initial_precision(assertion, has_summary);
  const unsigned last_assertion_loc = omega.get_last_assertion_loc();
  const bool single_assertion_check = omega.is_single_assertion_check();

  std::vector<unsigned> ints;
  get_ints(ints, options.get_option("part-itp"));
  symbol_tablet temp_table;
  namespacet ns{this->symbol_table, temp_table};

  prop_partitioning_target_equationt equation(ns, *summary_store, store_summaries_with_assertion);

#ifdef DISABLE_OPTIMIZATIONS
  if (options.get_bool_option("dump-SSA-tree")) {
    equation.set_dump_SSA_tree(true);
    equation.set_dump_SSA_tree_name(options.get_option("dump-query-name"));
  }
#endif
  
  call_tree_nodet& summary_info = omega.get_call_tree_root();
  symex_assertion_sumt symex {
            *summary_store, get_goto_functions(), summary_info, ns, temp_table,
            equation, message_handler, goto_program, last_assertion_loc,
            single_assertion_check, !no_slicing_option, !no_ce_option, 
            false, unwind_bound, partial_loops };

//  setup_unwind(symex);

  prop_refiner_assertion_sumt refiner = prop_refiner_assertion_sumt(
              *summary_store, omega,
              get_refine_mode(options.get_option("refine-mode")),
              message_handler, last_assertion_loc, true);

  prop_assertion_sumt prop = prop_assertion_sumt(equation, message_handler);
  unsigned count = 0;
  bool end = false;
  std::cout <<"";

  std::unique_ptr<prop_conv_solvert> decider_prop;
  std::unique_ptr<interpolating_solvert> interpolator;
  while (!end)
  {
    count++;
    
    // Init the next iteration context
    {
        assert(!options.get_bool_option("no-partitions")); // Cannot work with no-partition
        decider = (new satcheck_opensmt2t("prop checker"));
        initialize_solver_options(decider);

        interpolator.reset(decider);
        bv_pointerst *deciderp = new bv_pointerst(ns, *(dynamic_cast<satcheck_opensmt2t *> (decider)));
        deciderp->unbounded_array = bv_pointerst::unbounded_arrayt::U_AUTO;
        decider_prop.reset(deciderp);
    }
    
    end = (count == 1) ? symex.prepare_SSA(assertion) : symex.refine_SSA (refiner.get_refined_functions());

    if (!end){
      if (options.get_bool_option("claims-opt") && count == 1){
        prop_dependency_checkert(ns, message_handler, goto_program, omega, options.get_unsigned_int_option("claims-opt"), equation.SSA_steps.size())
                .do_it(equation);
        status() << (std::string("Ignored SSA steps after dependency checker: ") + std::to_string(equation.count_ignored_SSA_steps())) << eom;
      }

      end = prop.assertion_holds(assertion, ns, *(dynamic_cast<prop_conv_solvert *> (decider_prop.get())), *(interpolator.get())); // KE: strange conversion after shift to cbmc 5.5 - I think the bv_pointerst is changed
      unsigned summaries_count = omega.get_summaries_count();
      unsigned nondet_count = omega.get_nondets_count();
#ifdef PRODUCE_PROOF      
      if (end && interpolator->can_interpolate())
#else
      if (end)
#endif
      {
        if (options.get_bool_option("no-itp")){
          status() << ("Skip generating interpolants") << eom;
        } else {
#ifdef PRODUCE_PROOF            
          status() << ("Start generating interpolants...") << eom;
          extract_interpolants_prop(prop, equation, *decider_prop.get(), *interpolator.get());
#else
          assert(0);
#endif
        }
        if (summaries_count == 0)
        {
          status() << ("ASSERTION(S) HOLD(S) ") << eom; //TODO change the message to something more clear (like, everything was inlined...)
        } else {
          status() << "FUNCTION SUMMARIES (for " << summaries_count
        	   << " calls) WERE SUBSTITUTED SUCCESSFULLY." << eom;
        }
        report_success();
        status() << ("\n---Go to next assertion; claim verified by prop logic ---\n") <<eom;
      } else {
        if (summaries_count > 0 || nondet_count > 0) {
          if (summaries_count > 0){
            status() << "FUNCTION SUMMARIES (for " << summaries_count
                   << " calls) AREN'T SUITABLE FOR CHECKING ASSERTION." << eom;
          }
          if (nondet_count > 0){
            status() << "HAVOCING (of " << nondet_count
                   << " calls) AREN'T SUITABLE FOR CHECKING ASSERTION." << eom;
          }
          refiner.refine(*decider_prop, omega.get_call_tree_root(), equation);

          if (refiner.get_refined_functions().size() == 0){
            if (!options.get_bool_option("no-error-trace"))   
              prop.error_trace(*decider_prop, ns);
            status() << ("A real bug found.") << endl << eom;
            report_failure();
            status() << ("\n---Go to next assertion; claim checked by prop logic ---\n") <<eom;
            break;
          } else {
            //status("Counterexample is spurious");
            status() << ("Go to next iteration\n") << eom;
          }
        } else {
          if (!options.get_bool_option("no-error-trace"))
            prop.error_trace(*decider_prop, ns);
          status() << ("ASSERTION(S) DO(ES)N'T HOLD") << endl;
          status() << ("A real bug found") << endl << eom;
          report_failure();
          status() << ("\n---Go to next assertion; claim checked by prop logic ---\n") <<eom;
          break;
        }
      }
    }
      else{
        // end is true -> report success (It is needed when the assertion trivially holds)
        report_success();
        status() << ("\n---Go to next assertion; claim verified by prop logic ---\n") <<eom;
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

 Function: core_checkert::assertion_holds_smt

 Inputs:

 Outputs:

 Purpose: Helper function Checks if the given equation holds in smt encoding

\*******************************************************************/
/*namespace{
    bool is_satisfiable(smtcheck_opensmt2t & decider) {
        absolute_timet before, after;
        before=current_time();
        bool is_sat = decider.solve();
        after=current_time();
        //solving_time = (after-before);
        //for the report we should have proper method, since status cannot be used here directly
        status << "SOLVER TIME: " << (after-before) << eom;
        status() << "RESULT: ";

        // solve it
        if (!is_sat)
        {
            status() << "UNSAT - it holds!" << eom;
            return false;
        } else {
            status() << "SAT - doesn't hold" << eom;
            return true;
        }
        return is_sat;
    }
}*/
/*******************************************************************

 Function: core_checkert::assertion_holds_smt

 Inputs:

 Outputs:

 Purpose: Checks if the given assertion of the GP holds for smt encoding

\*******************************************************************/

bool core_checkert::assertion_holds_smt(const assertion_infot& assertion,
        bool store_summaries_with_assertion)
{
    absolute_timet initial, final;
    initial = current_time();
 
    // Init the objects:
    const bool no_slicing_option = options.get_bool_option("no-slicing");
    const bool no_ce_option = options.get_bool_option("no-error-trace");
    assert(options.get_option("logic") != "prop");
    const unsigned int unwind_bound = options.get_unsigned_int_option("unwind");

    // prepare omega
    const auto & const_summary_store = *summary_store;
    auto has_summary = [&const_summary_store](const std::string & function_name){
        return const_summary_store.has_summaries(function_name);
    };
    omega.set_initial_precision(assertion, has_summary);
    const unsigned last_assertion_loc = omega.get_last_assertion_loc();
    const bool single_assertion_check = omega.is_single_assertion_check();

    symbol_tablet temp_table;
    namespacet ns{this->symbol_table, temp_table};
    smt_partitioning_target_equationt equation(ns, *summary_store,
                                                store_summaries_with_assertion);

#ifdef DISABLE_OPTIMIZATIONS
    if (options.get_bool_option("dump-SSA-tree")) {
        equation.set_dump_SSA_tree(true);
        equation.set_dump_SSA_tree_name(options.get_option("dump-query-name"));
    }
#endif
  
    call_tree_nodet& call_tree_root = omega.get_call_tree_root();
    symex_assertion_sumt symex = symex_assertion_sumt(
            *summary_store, get_goto_functions(), call_tree_root, ns, temp_table,
            equation, message_handler, goto_program, last_assertion_loc,
            single_assertion_check, !no_slicing_option, !no_ce_option, true, unwind_bound,
            options.get_bool_option("partial-loops"));

    smt_refiner_assertion_sumt refiner = smt_refiner_assertion_sumt(
              *summary_store, omega,
              get_refine_mode(options.get_option("refine-mode")),
              message_handler, last_assertion_loc, true);

    prepare_smt_formulat ssaTosmt = prepare_smt_formulat(equation, message_handler);

    unsigned iteration_counter = 0;
    // in this phase we create SSA from the goto program, possibly skipping over some functions based on information in omega
    bool end = symex.prepare_SSA(assertion);

    if(!end && options.get_bool_option("claims-opt")){
        smt_dependency_checkert(ns, 
                    message_handler, 
                    goto_program, 
                    omega, 
                    options.get_unsigned_int_option("claims-opt"), 
                    equation.SSA_steps.size())
                .do_it(equation);
        status() << (std::string("Ignored SSA steps after dependency checker: ") + std::to_string(equation.count_ignored_SSA_steps())) << eom;
    }

    // the checker main loop:
    unsigned summaries_used = 0;
    while (!end) {
        iteration_counter++;

        //Converts SSA to SMT formula
        ssaTosmt.convert_to_formula( *(dynamic_cast<smtcheck_opensmt2t *> (decider)), *(decider));

        // Decides the equation
        bool is_sat = ssaTosmt.is_satisfiable(*(dynamic_cast<smtcheck_opensmt2t *> (decider)));
        summaries_used = omega.get_summaries_count();
        
        end = !is_sat;
        if (is_sat) {
        // check for possible refinement
    //      MB: TODO: get this schema working
    //      if(refiner.can_refine())
    //      {
    //        refiner.refine();
    //      }

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
            refiner.mark_sum_for_refine(*(dynamic_cast <smtcheck_opensmt2t *> (decider)), omega.get_call_tree_root(), equation);
            bool refined = !refiner.get_refined_functions().empty();
            if (!refined) {
                // nothing could be refined to rule out the cex, it is real -> break out of refinement loop
                break;
            } else {
                // REPORT
                status() << ("Go to next iteration\n") << eom;

                // do the actual refinement of ssa
                symex.refine_SSA(refiner.get_refined_functions());
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
            if (decider->can_interpolate()) {
            #ifdef PRODUCE_PROOF            
                status() << ("Start generating interpolants...") << eom;
                extract_interpolants_smt(ssaTosmt, equation);
            #else
                assert(0); // Cannot produce proof in that case!
            #endif
            } else {
                status() << ("Skip generating interpolants") << eom;
            }
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
        assertion_violated(ssaTosmt, symex.guard_expln);
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
  
  const bool no_slicing_option = options.get_bool_option("no-slicing");
//  const bool no_ce_option = options.get_bool_option("no-error-trace");

    const auto & const_summary_store = *summary_store;
    auto has_summary = [&const_summary_store](const std::string & function_name){
        return const_summary_store.has_summaries(function_name);
    };
  omega.set_initial_precision(assertion, has_summary);
  const unsigned last_assertion_loc = omega.get_last_assertion_loc();
//  const bool single_assertion_check = omega.is_single_assertion_check();

  std::vector<unsigned> ints;
  get_ints(ints, options.get_option("part-itp"));
  
  // KE:  remove the message once smt_symex_target_equationt supports interpolation
  // Notify that there is no support to interpolations
  status() << "--no-partition activates also --no-itp flag, as there is no (yet) support for summaries/interpolations in this version" << eom;

  symbol_tablet temp_table;
  namespacet ns {this->symbol_table, temp_table};

  smt_symex_target_equationt equation(ns, ints);
#ifdef DISABLE_OPTIMIZATIONS
  if (options.get_bool_option("dump-SSA-tree")) {
    equation.set_dump_SSA_tree(true);
    equation.set_dump_SSA_tree_name(options.get_option("dump-query-name"));
  }
#endif
  
  symex_no_partitiont symex = symex_no_partitiont(ns, temp_table, equation, message_handler, goto_program,!no_slicing_option);
  
  setup_unwind(symex);
  
  // KE: I think this says the same
  smt_refiner_assertion_sumt refiner = smt_refiner_assertion_sumt(
              *summary_store, omega,
              get_refine_mode(options.get_option("refine-mode")),
              message_handler, last_assertion_loc, true);


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
        smt_dependency_checkert(ns, message_handler, goto_program, omega, options.get_unsigned_int_option("claims-opt"), equation.SSA_steps.size())
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
void core_checkert::assertion_violated (prepare_smt_formulat& prop,
				std::map<irep_idt, std::string> &guard_expln)
{
    smtcheck_opensmt2t* decider_smt = dynamic_cast <smtcheck_opensmt2t*> (decider);
    namespacet ns{this->symbol_table};

    if (!options.get_bool_option("no-error-trace"))
        prop.error_trace(*decider_smt, ns, guard_expln);
    if (decider_smt->has_unsupported_vars()){
    	status() << "\nA bug found." << endl;
    	status() << "WARNING: Possibly due to the Theory conversion." << eom;
    } else {
    	status() << "A real bug found." << eom;
    }
    report_failure();

    decider_smt = nullptr;
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
    namespacet ns{this->symbol_table};
    if (!options.get_bool_option("no-error-trace"))
        prop.error_trace(*decider_smt, ns, guard_expln);
    if (decider_smt->has_unsupported_vars()){
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
void core_checkert::extract_interpolants_smt (prepare_smt_formulat& prop, smt_partitioning_target_equationt& equation)
{
  //SA & prop is not needed here; the entire class prepare_smt_formulat is useless.
  absolute_timet before, after;
  before=current_time();
  
  smtcheck_opensmt2t* decider_smt = dynamic_cast <smtcheck_opensmt2t*> (decider);
  equation.extract_interpolants(*decider_smt);
  decider_smt = nullptr;

  after=current_time();
  status() << "INTERPOLATION TIME: " << (after-before) << eom;
  
  // Store the summaries
  const std::string& summary_file = options.get_option("save-summaries");
  if (!summary_file.empty()) {
    std::ofstream out;
    out.open(summary_file.c_str());
    decider->getLogic()->dumpHeaderToFile(out);
    summary_store->serialize(out);
  }
}

/*******************************************************************\

Function: core_checkert::extract_interpolants_prop

  Inputs:

 Outputs:

 Purpose: Extract and store the interpolation summaries for prop only

\*******************************************************************/
void core_checkert::extract_interpolants_prop (prop_assertion_sumt& prop, prop_partitioning_target_equationt& equation,
            prop_conv_solvert& decider_prop, interpolating_solvert& interpolator)
{
  absolute_timet before, after;
  before=current_time();

  equation.extract_interpolants(interpolator, decider_prop);

  after=current_time();
  status() << "INTERPOLATION TIME: " << (after-before) << eom;
  
  // Store the summaries
  std::string summary_file;
#ifdef PRODUCE_PROOF  
  if(options.get_bool_option("sum-theoref")) {
      summary_file = "__summaries_prop";
  }
  else {
      summary_file = options.get_option("save-summaries");
  }
#else
  summary_file = options.get_option("save-summaries");
#endif
  if (!summary_file.empty()) {
    std::ofstream out;
    out.open(summary_file.c_str());
    summary_store->serialize(out);
  }
}
#endif

/*******************************************************************\

Function: core_checkert::setup_unwind

  Inputs:

 Outputs:

 Purpose: Setup the unwind bounds.

\*******************************************************************/

void core_checkert::setup_unwind(symex_bmct& symex)
{
  const std::string &set=options.get_option("unwindset");
  unsigned int length=set.length();

  for(unsigned int idx=0; idx<length; idx++)
  {
    std::string::size_type next=set.find(",", idx);
    std::string val=set.substr(idx, next-idx);

    if(val.rfind(":")!=std::string::npos)
    {
      std::string id=val.substr(0, val.rfind(":"));
      unsigned long uw=atol(val.substr(val.rfind(":")+1).c_str());
      //symex.unwind_set[id]=uw; // KE: changed in cbmc 5.5
      symex.set_unwind_thread_loop_limit(1,id,uw); //KE: No threads support, assume main is in thread 1
    }
    
    if(next==std::string::npos) break;
    idx=next;
  }

  symex.set_unwind_limit(options.get_unsigned_int_option("unwind"));
}

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
namespace{
//Purpose: extracts summaries after successful verification; and dumps the summaries
// in a specific summary-file for uf and lra separately based on the solver.

    void extract_and_store_summaries(smt_partitioning_target_equationt & equation, summary_storet & store,
                                      smtcheck_opensmt2t & decider , string & summary_file_name){
        equation.extract_interpolants(decider);

        // Store the summaries
        if (!summary_file_name.empty()) {
            std::ofstream out;
            out.open(summary_file_name.c_str());
            // TODO: find out how to dump bear minimum
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
            smtcheck_opensmt2t & decider, smtcheck_opensmt2t & prev_solver) {
        
        // Detect if there are non-linear parts:
        std::set<PTRef>* non_linears = prev_solver.get_non_linears();
        if (non_linears->size() > 0)
        {
            // Notify the user
            std::cerr << "Non linear operation encounter. Ignoring " << non_linears->size() << " expressions in the file.\n";
            
            // Fix the summaries
            std::stringstream dump;
            dump << decider.getSimpleHeader();
            store.serialize(dump);
            std::string sm = dump.str();
            
            // Replace all non-linear expressions in unsupported variable
            string new_token = decider.create_new_unsupported_var("_sumref", true); // unsupported operator symbol name 
            for(std::set<PTRef>::iterator nl = non_linears->begin(); nl != non_linears->end(); nl++)
            {
                // Get the old token we wish to abstract
                char* token = prev_solver.getLogic()->printTerm(*nl);
                string old_token(token);

                // Add the declaration to in the solver
                prev_solver.getLogic()->mkVar(prev_solver.getLogic()->getSortRef(*nl), (prev_solver.create_new_unsupported_var("_sumref", false)).c_str());
                prev_solver.getLogic()->mkVar(prev_solver.getLogic()->getSortRef(*nl), (prev_solver.create_new_unsupported_var("_sumref", true)).c_str());
                //decider.getLogic()->mkVar(decider.getLogic()->getSortRef(*nl), (decider.create_new_unsupported_var("_sumref", false)).c_str());
                
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
                        //std::cout << "** Replace : " << id_str_SSA << " in " << id_str_curr << std::endl;
                        
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
                //std::cout << "Replacing " << old_token << " in " << new_token << std::endl;
                free(token); token = NULL;
            }
            //std::cout << ";; Summary is " << sm << std::endl;
            
            // Clean the data in use
            delete(non_linears);
            
            // Store to Temp. file
            std::ofstream out;
            out.open("__summaries_linear_temp");
            // TODO: find out how to dump bear minimum
            //dumps define-fun()  into summary file
            out << prev_solver.getSimpleHeader() << sm;
            out.close();
            
            std::vector<std::string> filenames_linear;
            filenames_linear.insert(filenames_linear.begin(), filenames.begin(), filenames.end());
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
    void reset_partition_summary_info(smt_partitioning_target_equationt & eq, smt_summary_storet const & store) {
        for (auto & partition : eq.get_partitions()){
            // check if we have summary in the store for this partition
            const auto & function_name = id2string(partition.get_iface().function_id);
            bool should_summarize = partition.get_iface().call_tree_node.get_precision() == summary_precisiont::SUMMARY;
            // should_summarize -> store.has_summaries
            assert(!should_summarize || store.has_summaries(function_name));
            bool was_summarized = partition.summary;
            if(should_summarize){
                // clear the old information and load new information from the store
                // fill the partition with new summaries
                eq.fill_summary_partition(partition.get_iface().partition_id, store.get_summaries(function_name));
                assert(partition.summary);
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
/*******************************************************************\

Function: core_checkert::check_sum_theoref_single

  Inputs:

 Outputs:

 Purpose: main method to make summary-ref and theory-ref work together

\*******************************************************************/
#ifdef PRODUCE_PROOF
bool core_checkert::check_sum_theoref_single(const assertion_infot &assertion)
{
    std::string lra_summary_file_name {"__summaries_lra"};
    std::string uf_summary_file_name {"__summaries_uf"};
    smtcheck_opensmt2t_uf uf_solver {"uf checker"};
    initialize_solver_options(&uf_solver);

    smt_summary_storet summary_store {&uf_solver};
    //reading summary by uf
    status() << "\n--Reading UF summary file: " << uf_summary_file_name << eom;
    summary_store.deserialize({uf_summary_file_name});
    const auto & const_summary_store = summary_store;
    auto has_summary = [&const_summary_store]
            (const std::string & function_name){
        return const_summary_store.has_summaries(function_name);
    };
    omega.set_initial_precision(assertion, has_summary);
    symbol_tablet temp_table;
    namespacet ns{this->symbol_table, temp_table};
    smt_partitioning_target_equationt equation {ns, summary_store, false};

    symex_assertion_sumt symex {summary_store,
                                get_goto_functions(),
                                omega.get_call_tree_root(),
                                ns,
                                temp_table,
                                equation,
                                message_handler,
                                goto_program,
                                omega.get_last_assertion_loc(),
                                omega.is_single_assertion_check(),
                                !options.get_bool_option("no-slicing"),
                                !options.get_bool_option("no-error-trace"),
                                true,
                                options.get_unsigned_int_option("unwind"),
                                options.get_bool_option("partial-loops"),
    };

    bool assertion_holds = symex.prepare_SSA(assertion);
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
    smt_refiner_assertion_sumt localRefine{summary_store, omega,
                                           refinement_modet::SLICING_RESULT,
                                           this->get_message_handler(),
                                           omega.get_last_assertion_loc(), true};


    localRefine.mark_sum_for_refine(uf_solver, omega.get_call_tree_root(), equation);
    bool can_refine = !localRefine.get_refined_functions().empty();
    while(can_refine) {
        symex.refine_SSA(localRefine.get_refined_functions());
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
    smtcheck_opensmt2t_lra lra_solver {0, "lra checker"}; //TODO: type_constraints_level
    initialize_solver_options(&lra_solver);
    status() << "\n--Reading LRA and UF summary files: " << uf_summary_file_name << "," << lra_summary_file_name << eom;
    reload_summaries(ns, summary_store, {uf_summary_file_name, lra_summary_file_name}, lra_solver, uf_solver );
    omega.set_initial_precision(assertion, has_summary);
    reset_partition_summary_info(equation, summary_store);
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
        symex.refine_SSA(localRefine.get_refined_functions());
        // new lra_solver here, because of LRA incrementality problems in OpenSMT
        smtcheck_opensmt2t_lra lra_solver2 {0, "lra checker (in loop)"};
        initialize_solver_options(&lra_solver2);
        // we have new solver, but summary store has references from the old solver, we need to reload
        status() << "\n--Reading LRA and UF summary files: " << uf_summary_file_name << "," << lra_summary_file_name << eom;
        reload_summaries(ns, summary_store, {uf_summary_file_name, lra_summary_file_name}, lra_solver2, uf_solver);
        equation.convert(lra_solver2, lra_solver2);
        is_sat = lra_solver2.solve();
        if(!is_sat){
            extract_and_store_summaries(equation, summary_store, lra_solver2, lra_summary_file_name);
            // report results
            report_success();
            status() << ("\n---Go to next assertion; claim verified by LRA with some local Refinement---\n") << eom;
            return true; // claim verified by LRA encoding -> go to next claim
        }
        localRefine.mark_sum_for_refine(lra_solver2, omega.get_call_tree_root(), equation);
        can_refine = !localRefine.get_refined_functions().empty();
    }
//---------------------------------------------------------------------------
    // call theory refinement
  /*  status() << "\n---EUF and LRA were not enough; trying to refine with theory-refinement using CUF + BV ---\n" <<eom;
    // MB: we need fresh secondary table for the symex in the theory refiner
    theory_refinert th_checker(this->goto_program,
                               get_goto_functions(),
                               this->symbol_table,
                               options,
                               message_handler);
    th_checker.initialize();
    return th_checker.assertion_holds_smt(assertion, false);*/

    //cal prop --------------------------------------------------------------------------
    status() << "\n---EUF and LRA were not enough; trying to use prop logic ---\n" <<eom;
    std::string prop_summary_filename {"__summaries_prop"};

    this->summary_store.reset(new prop_summary_storet());
    ifstream f(prop_summary_filename.c_str());
    if (f.good()) {
        status() << "\n--Reading Prop summary file: " << prop_summary_filename <<"\n" << eom;
        this->summary_store->deserialize(std::vector<std::string>{prop_summary_filename});
    }
    return this->assertion_holds_prop(assertion, false);
}
#endif
