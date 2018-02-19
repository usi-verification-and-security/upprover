/*******************************************************************

 Module: Assertion checker that extracts and uses function 
 summaries

 Author: Ondrej Sery

\*******************************************************************/
#include "summarizing_checker.h"
#include "dependency_checker.h"

#include "solvers/smtcheck_opensmt2_lra.h"
#include "solvers/smtcheck_opensmt2_cuf.h"
#include "solvers/smtcheck_opensmt2_uf.h"
#include "smt_refiner_assertion_sum.h"
#include "prop_refiner_assertion_sum.h"
#include "smt_dependency_checker.h"
#include "prop_dependency_checker.h"
#include "nopartition/symex_no_partition.h"
#include "prop_summary_store.h"
#include "partition_iface.h"
#include "nopartition/smt_assertion_no_partition.h"
#include "prop_partitioning_target_equation.h"
#include "smt_partitioning_target_equation.h"
#include "prop_assertion_sum.h"
#include "prepare_smt_formula.h"
#include "symex_assertion_sum.h"
#include <solvers/flattening/bv_pointers.h>


void summarizing_checkert::initialize_solver()
{
    string _logic = options.get_option("logic");
    int _type_constraints = options.get_unsigned_int_option("type-constraints");
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
        decider = new smtcheck_opensmt2t_lra(_type_constraints, "lra checker");
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
  
  // Set all the rest of the option - KE: check what to shift to the part of SMT only
  decider->set_verbosity(options.get_unsigned_int_option("verbose-solver"));
#ifdef PRODUCE_PROOF   
  decider->set_itp_bool_alg(options.get_unsigned_int_option("itp-algorithm"));
  decider->set_itp_euf_alg(options.get_unsigned_int_option("itp-uf-algorithm"));
  decider->set_itp_lra_alg(options.get_unsigned_int_option("itp-lra-algorithm"));
  if(options.get_option("itp-lra-factor").size() > 0) 
      decider->set_itp_lra_factor(options.get_option("itp-lra-factor").c_str());
  decider->set_certify(options.get_unsigned_int_option("check-itp"));
  if(options.get_bool_option("reduce-proof"))
  {
    decider->set_reduce_proof(options.get_bool_option("reduce-proof"));
    if(options.get_unsigned_int_option("reduce-proof-graph")) decider->set_reduce_proof_graph(options.get_unsigned_int_option("reduce-proof-graph"));
    if(options.get_unsigned_int_option("reduce-proof-loops")) decider->set_reduce_proof_loops(options.get_unsigned_int_option("reduce-proof-loops"));
  }
#endif
  if(options.get_unsigned_int_option("random-seed")) decider->set_random_seed(options.get_unsigned_int_option("random-seed"));
#ifdef DISABLE_OPTIMIZATIONS  
  if (options.get_bool_option("dump-query"))
      decider->set_dump_query(true);
  if (options.get_bool_option("dump-pre-query"))
      decider->set_dump_pre_query(true);
  decider->set_dump_query_name(options.get_option("dump-query-name"));
#endif  
}

void summarizing_checkert::initialize()
{
    initialize_solver();
  
    // Init the summary storage
    // Prop and SMT have different mechanism to load/store summaries
    // TODO: unify this mechanism
    if (options.get_option("logic") == "prop")
        summarization_context.set_summary_store(new prop_summary_storet());
    else
        summarization_context.set_summary_store(new smt_summary_storet());
  
    // Prepare the summarization context
    summarization_context.analyze_functions(ns);

    // Load older summaries
    {
        //TODO: MB: How about checking if this file actually exists?
        const std::string& summary_file = options.get_option("load-summaries");
        if (!summary_file.empty()) {
            // Prop and SMT have different mechanism to load/store summaries
            // TODO: unify this mechanism
            if (options.get_option("logic") == "prop")
                summarization_context.deserialize_infos_prop(summary_file); // Prop load summary  
            else
                summarization_context.deserialize_infos_smt(summary_file, dynamic_cast <smtcheck_opensmt2t*> (decider)); // smt load summary
        }
    }

  // Prepare summary_info (encapsulated in omega), start with the lazy variant,
  // i.e., all summaries are initialized as HAVOC, except those on the way
  // to the target assertion, which are marked depending on initial mode.

  omega.initialize_summary_info (omega.get_summary_info(), goto_program);
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

 Function: summarizing_checkert::assertion_holds

 Inputs:

 Outputs:

 Purpose: Checks if the given assertion of the GP holds

\*******************************************************************/

bool summarizing_checkert::assertion_holds(const assertion_infot& assertion,
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
            "\n  " << from_expr(ns, "", assertion.get_location()->guard)  
            << eom;
#endif
    
    return true;
  }
  
  // TODO: need to split this class and create a version for prop and smt
  // Unless we wish to unify mechanism also for error_trace!
  if (options.get_option("logic") == "prop")
    return assertion_holds_prop(assertion, store_summaries_with_assertion);
  else if (options.get_bool_option("no-partitions")) // BMC alike version
    return assertion_holds_smt_no_partition(assertion, store_summaries_with_assertion); 
  else 
    return assertion_holds_smt(assertion, store_summaries_with_assertion);
}

/*******************************************************************

 Function: summarizing_checkert::assertion_holds

 Inputs:

 Outputs:

 Purpose: Checks if the given assertion of the GP holds for prop logic

\*******************************************************************/

bool summarizing_checkert::assertion_holds_prop(const assertion_infot& assertion,
        bool store_summaries_with_assertion)
{
  absolute_timet initial, final;
  initial=current_time();
  
  const bool no_slicing_option = options.get_bool_option("no-slicing");
  const bool no_ce_option = options.get_bool_option("no-error-trace");
  assert(options.get_option("logic") == "prop");
  const unsigned int unwind_bound = options.get_unsigned_int_option("unwind");
  const bool partial_loops = options.get_bool_option("partial-loops");

  omega.set_initial_precision(assertion);
  const unsigned last_assertion_loc = omega.get_last_assertion_loc();
  const bool single_assertion_check = omega.is_single_assertion_check();

  std::vector<unsigned> ints;
  get_ints(ints, options.get_option("part-itp"));

  prop_partitioning_target_equationt equation(ns, summarization_context, store_summaries_with_assertion);

#ifdef DISABLE_OPTIMIZATIONS
  if (options.get_bool_option("dump-SSA-tree")) {
    equation.set_dump_SSA_tree(true);
    equation.set_dump_SSA_tree_name(options.get_option("dump-query-name"));
  }
#endif
  
  summary_infot& summary_info = omega.get_summary_info();
  symex_assertion_sumt symex {
            summarization_context, summary_info, ns, symbol_table,
            equation, message_handler, goto_program, last_assertion_loc,
            single_assertion_check, !no_slicing_option, !no_ce_option, 
            false, unwind_bound, partial_loops };

//  setup_unwind(symex);

  prop_refiner_assertion_sumt refiner = prop_refiner_assertion_sumt(
              summarization_context, omega,
              get_refine_mode(options.get_option("refine-mode")),
              message_handler, last_assertion_loc, true);

  prop_assertion_sumt prop = prop_assertion_sumt(summarization_context,
          equation, message_handler, max_memory_used);
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
        decider = (new satcheck_opensmt2t("sat checker"))->set_prop_conv_solver(
                (dynamic_cast<prop_conv_solvert *> (decider_prop.get())));

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
          extract_interpolants_prop(prop, equation, decider_prop, interpolator);
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
          refiner.refine(*decider_prop, omega.get_summary_info(), equation);

          if (refiner.get_refined_functions().size() == 0){
            prop.error_trace(*decider_prop, ns);
            status() << ("A real bug found.") << endl << eom;
            report_failure();
            break;
          } else {
            //status("Counterexample is spurious");
            status() << ("Go to next iteration\n") << eom;
          }
        } else {
          prop.error_trace(*decider_prop, ns);
          status() << ("ASSERTION(S) DO(ES)N'T HOLD") << endl;
          status() << ("A real bug found") << endl << eom;
          report_failure();
          break;
        }
      }
    }
      else{
        // end is true -> report success (It is needed when the assertion trivially holds)
        report_success();
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

 Function: summarizing_checkert::assertion_holds_smt

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

 Function: summarizing_checkert::assertion_holds_smt

 Inputs:

 Outputs:

 Purpose: Checks if the given assertion of the GP holds for smt encoding

\*******************************************************************/

bool summarizing_checkert::assertion_holds_smt(const assertion_infot& assertion,
        bool store_summaries_with_assertion)
{
  absolute_timet initial, final;
  initial = current_time();
  
  const bool no_slicing_option = options.get_bool_option("no-slicing");
  const bool no_ce_option = options.get_bool_option("no-error-trace");
  assert(options.get_option("logic") != "prop");
  const unsigned int unwind_bound = options.get_unsigned_int_option("unwind");

  // prepare omega
  omega.set_initial_precision(assertion);
  const unsigned last_assertion_loc = omega.get_last_assertion_loc();
  const bool single_assertion_check = omega.is_single_assertion_check();

  smt_partitioning_target_equationt equation(ns, summarization_context,
      store_summaries_with_assertion);

#ifdef DISABLE_OPTIMIZATIONS
  if (options.get_bool_option("dump-SSA-tree")) {
    equation.set_dump_SSA_tree(true);
    equation.set_dump_SSA_tree_name(options.get_option("dump-query-name"));
  }
#endif
  
  summary_infot& summary_info = omega.get_summary_info();
  symex_assertion_sumt symex = symex_assertion_sumt(
            summarization_context, summary_info, ns, symbol_table,
            equation, message_handler, goto_program, last_assertion_loc,
            single_assertion_check, !no_slicing_option, !no_ce_option, true, unwind_bound,
            options.get_bool_option("partial-loops"));

  smt_refiner_assertion_sumt refiner = smt_refiner_assertion_sumt(
              summarization_context, omega,
              get_refine_mode(options.get_option("refine-mode")),
              message_handler, last_assertion_loc, true);

  prepare_smt_formulat ssaToSmt = prepare_smt_formulat(summarization_context,
          equation, message_handler, max_memory_used);


  unsigned iteration_counter = 0;
  // in this phase we create SSA from the goto program, possibly skipping over some functions based on information in omega
  bool end = symex.prepare_SSA(assertion);

//  MB: This should be handled elsewhere. Disabling option 'list-templates' until handled properly
//  //LA: good place?
//  if(options.get_bool_option("list-templates"))
//  {
//    status() << "Listing templates\n" << eom;
//    list_templates(prop, equation);
//    return true;
//  }

  //
  if(!end && options.get_bool_option("claims-opt")){
    smt_dependency_checkert(ns, message_handler, goto_program, omega, options.get_unsigned_int_option("claims-opt"), equation.SSA_steps.size())
      .do_it(equation);
    status() << (std::string("Ignored SSA steps after dependency checker: ") + std::to_string(equation.count_ignored_SSA_steps())) << eom;
  }

  while (!end) {
    iteration_counter++;

    //Converts SSA to SMT formula
    ssaToSmt.convert_to_formula( *(dynamic_cast<smtcheck_opensmt2t *> (decider)), *(decider));

    // Decides the equation
    bool is_sat = ssaToSmt.is_satisfiable(*(dynamic_cast<smtcheck_opensmt2t *> (decider)));

    end = !is_sat;
    if (is_sat) {
      // check for possible refinement
//      MB: TODO: get this schema working
//      if(refiner.can_refine())
//      {
//        refiner.refine();
//      }
      // this refiner can refine if we have summary or havoc representation of a function
      if (omega.get_summaries_count() > 0 || omega.get_nondets_count() > 0) {
        // REPORT part
        {
          const unsigned int summaries_used = omega.get_summaries_count();
          if (summaries_used > 0){
            status() << "FUNCTION¸ SUMMARIES (for " << summaries_used << " calls) AREN'T SUITABLE FOR CHECKING ASSERTION." << eom;
          }
          const unsigned int nondet_used = omega.get_nondets_count();
          if (nondet_used > 0){
            status() << "HAVOCING (of " << nondet_used << " calls) AREN'T SUITABLE FOR CHECKING ASSERTION." << eom;
          }
        } // END of REPORT

        // figure out functions that can be refined
        refiner.refine(*(dynamic_cast <smtcheck_opensmt2t *> (decider)), omega.get_summary_info(), equation);
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
      else {
        // nothing left to refine, cex is real -> break out of the refinement loop
        break;
      }
    }
  } // end of refinement loop
  // the assertion has been successfully verified if we have (end == true)
  const bool is_verified = end;
  if (is_verified) {
    // produce and store the summaries
    if (!options.get_bool_option("no-itp")) {
#ifdef PRODUCE_PROOF
      if (decider->can_interpolate()) {
        status() << ("Start generating interpolants...") << eom;
        extract_interpolants_smt(ssaToSmt, equation);
      }
#else
      // if PRODUCE_PROOF is not defined, we should always use no-itp
      assert(false);
#endif
    } else {
      status() << ("Skip generating interpolants") << eom;
    }
    // report results
    if(omega.get_summaries_count() > 0) {
      status() << "FUNCTION SUMMARIES (for " << omega.get_summaries_count()
               << " calls) WERE SUBSTITUTED SUCCESSFULLY." << eom;
    }
    report_success();
  }
  else // assertion was falsified
  {
    assertion_violated(ssaToSmt, symex.guard_expln);
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

 Function: summarizing_checkert::assertion_holds_smt_no_partition

 Inputs:

 Outputs:

 Purpose: Checks if the given assertion of the GP holds for smt encoding

\*******************************************************************/

bool summarizing_checkert::assertion_holds_smt_no_partition(
        const assertion_infot& assertion,
        bool store_summaries_with_assertion)
{
  absolute_timet initial, final;
  initial=current_time();
  
  const bool no_slicing_option = options.get_bool_option("no-slicing");
  const bool no_ce_option = options.get_bool_option("no-error-trace");

  omega.set_initial_precision(assertion);
  const unsigned last_assertion_loc = omega.get_last_assertion_loc();
  const bool single_assertion_check = omega.is_single_assertion_check();

  std::vector<unsigned> ints;
  get_ints(ints, options.get_option("part-itp"));
  
  // KE:  remove the message once smt_symex_target_equationt supports interpolation
  // Notify that there is no support to interpolations
  status() << "--no-partition activates also --no-itp flag, as there is no (yet) support for summaries/interpolations in this version" << eom;
  
  smt_symex_target_equationt equation(ns, ints);
#ifdef DISABLE_OPTIMIZATIONS
  if (options.get_bool_option("dump-SSA-tree")) {
    equation.set_dump_SSA_tree(true);
    equation.set_dump_SSA_tree_name(options.get_option("dump-query-name"));
  }
#endif
  
  symex_no_partitiont symex = symex_no_partitiont(ns, 
            symbol_table,
            equation, message_handler, goto_program, last_assertion_loc,
            single_assertion_check, !no_slicing_option, !no_ce_option);
  
  setup_unwind(symex);
  
  // KE: I think this says the same
  smt_refiner_assertion_sumt refiner = smt_refiner_assertion_sumt(
              summarization_context, omega,
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
            ? symex.prepare_SSA(assertion, summarization_context.get_functions()) 
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
          refiner.refine(*(dynamic_cast <smtcheck_opensmt2t*> (decider)), omega.get_summary_info(), equation);

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

 Function: summarizing_checkert::assertion_violated

 Inputs:

 Outputs:

 Purpose: Prints the error trace for smt encoding

\*******************************************************************/
void summarizing_checkert::assertion_violated (prepare_smt_formulat& prop,
				std::map<irep_idt, std::string> &guard_expln)
{
    smtcheck_opensmt2t* decider_smt = dynamic_cast <smtcheck_opensmt2t*> (decider);

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

 Function: summarizing_checkert::assertion_violated

 Inputs:

 Outputs:

 Purpose: Prints the error trace for smt encoding

\*******************************************************************/
void summarizing_checkert::assertion_violated (smt_assertion_no_partitiont& prop,
				std::map<irep_idt, std::string> &guard_expln)
{
    smtcheck_opensmt2t* decider_smt = dynamic_cast <smtcheck_opensmt2t*> (decider);

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

// MB: not used at the moment
//// Only for SMT version
//void summarizing_checkert::list_templates(prepare_smt_formulat& prop, smt_partitioning_target_equationt& equation)
//{
//    summary_storet* summary_store = summarization_context.get_summary_store();
//    std::vector<summaryt*> templates;
//    smtcheck_opensmt2t* decider_smt = dynamic_cast <smtcheck_opensmt2t*> (decider);
//    equation.fill_function_templates(*decider_smt, templates);
//    decider_smt = nullptr;
//    for(unsigned int i = 0; i < templates.size(); ++i) {
//        summary_store->insert_summary(*templates[i]);
//    }
//    // Store the summaries
//    const std::string& summary_file = options.get_option("save-summaries");
//    if (!summary_file.empty()) {
//        summarization_context.serialize_infos_smt(summary_file,
//            omega.get_summary_info());
//    }
//}

#ifdef PRODUCE_PROOF
/*******************************************************************\

Function: summarizing_checkert::extract_interpolants_smt

  Inputs:

 Outputs:

 Purpose: Extract and store the interpolation summaries for smt only

\*******************************************************************/
void summarizing_checkert::extract_interpolants_smt (prepare_smt_formulat& prop, smt_partitioning_target_equationt& equation)
{
  summary_storet* summary_store = summarization_context.get_summary_store();
  interpolant_mapt itp_map;
  absolute_timet before, after;
  before=current_time();
  
  smtcheck_opensmt2t* decider_smt = dynamic_cast <smtcheck_opensmt2t*> (decider);
  equation.extract_interpolants(*decider_smt, itp_map);
  decider_smt = nullptr;

  after=current_time();
  status() << "INTERPOLATION TIME: " << (after-before) << eom;

  for (interpolant_mapt::iterator it = itp_map.begin();
                  it != itp_map.end(); ++it) {
    summary_infot& summary_info = it->first->summary_info;

    function_infot& function_info =
            summarization_context.get_function_info(
            summary_info.get_function_id());

    // MB TODO: check if this summary is not already in the store! (or do even more aggresive optimizations of the store
    function_info.add_summary(*summary_store, it->second, false);
           // !options.get_bool_option("no-summary-optimization"));
    
    summary_info.add_used_summary(it->second);
    summary_info.set_summary();           // helpful flag for omega's (de)serialization
  }
  
  // Store the summaries
  const std::string& summary_file = options.get_option("save-summaries");
  if (!summary_file.empty()) {
    std::ofstream out;
    out.open(summary_file.c_str());
    decider->getLogic()->dumpHeaderToFile(out);
    summarization_context.serialize_infos_smt(out, omega.get_summary_info());
  }
}

/*******************************************************************\

Function: summarizing_checkert::extract_interpolants_prop

  Inputs:

 Outputs:

 Purpose: Extract and store the interpolation summaries for prop only

\*******************************************************************/
void summarizing_checkert::extract_interpolants_prop (prop_assertion_sumt& prop, prop_partitioning_target_equationt& equation,
            std::unique_ptr<prop_conv_solvert>& decider_prop, std::unique_ptr<interpolating_solvert>& interpolator)
{
  summary_storet* summary_store = summarization_context.get_summary_store();
  interpolant_mapt itp_map;
  absolute_timet before, after;
  before=current_time();

  equation.extract_interpolants(*(interpolator.get()), *(dynamic_cast<prop_conv_solvert *> (decider_prop.get())), itp_map); // KE: strange conversion after shift to cbmc 5.5 - I think the bv_pointerst is changed

  after=current_time();
  status() << "INTERPOLATION TIME: " << (after-before) << eom;

  for (interpolant_mapt::iterator it = itp_map.begin();
                  it != itp_map.end(); ++it) {
    summary_infot& summary_info = it->first->summary_info;

    function_infot& function_info =
            summarization_context.get_function_info(
            summary_info.get_function_id());

    function_info.add_summary(*summary_store, it->second, false);
            //!options.get_bool_option("no-summary-optimization")*/);
    
    summary_info.add_used_summary(it->second);
    summary_info.set_summary();           // helpful flag for omega's (de)serialization
  }
  
  // Store the summaries
  const std::string& summary_file = options.get_option("save-summaries");
  if (!summary_file.empty()) {
    summarization_context.serialize_infos_prop(summary_file, 
        omega.get_summary_info());
  }
}
#endif

/*******************************************************************\

Function: summarizing_checkert::setup_unwind

  Inputs:

 Outputs:

 Purpose: Setup the unwind bounds.

\*******************************************************************/

void summarizing_checkert::setup_unwind(symex_bmct& symex)
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
};

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
};


coloring_modet get_coloring_mode(const std::string& str)
{
  if (str == "0"){
    return coloring_modet::RANDOM_COLORING;
  } else if (str == "1"){
    return coloring_modet::COLORING_FROM_FILE;
  } else {
    // by default
    return coloring_modet::NO_COLORING;
  }
};

/*******************************************************************\

Function: summarizing_checkert::report_success

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summarizing_checkert::report_success()
{
  //result() << ("VERIFICATION SUCCESSFUL");

  switch(message_handler.get_ui())
  {
  
    case ui_message_handlert::uit::PLAIN:
	result() << "\n\nVERIFICATION SUCCESSFUL" << eom;
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

Function: summarizing_checkert::report_failure

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void summarizing_checkert::report_failure()
{
  switch(message_handler.get_ui())
  {

    case ui_message_handlert::uit::PLAIN:
	result() << "\n\nVERIFICATION FAILED" << eom;;
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
