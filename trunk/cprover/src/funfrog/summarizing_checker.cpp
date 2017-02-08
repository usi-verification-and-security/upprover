/*******************************************************************

 Module: Assertion checker that extracts and uses function 
 summaries

 Author: Ondrej Sery

\*******************************************************************/
#include "summarizing_checker.h"
#include "partitioning_slice.h"
#include "dependency_checker.h"

#include "solvers/smtcheck_opensmt2_lra.h"
#include "solvers/smtcheck_opensmt2_cuf.h"
#include "solvers/smtcheck_opensmt2_uf.h"
#include "smt_refiner_assertion_sum.h"
#include "prop_refiner_assertion_sum.h"
#include "smt_dependency_checker.h"
#include "prop_dependency_checker.h"

void summarizing_checkert::initialize_solver()
{
    string _logic = options.get_option("logic");
    int _type_constraints = options.get_unsigned_int_option("type-constraints");
    if(_logic == "qfuf")
        decider = new smtcheck_opensmt2t_uf();
    else if(_logic == "qfcuf")
        decider = new smtcheck_opensmt2t_cuf(options.get_unsigned_int_option("bitwidth"));
    else if(_logic == "qflra")
        decider = new smtcheck_opensmt2t_lra(_type_constraints);
    else if (_logic == "prop")
        decider = new satcheck_opensmt2t();
    else 
    {
        std::cout << ("Unsupported theory: " +  _logic + "\n");
        assert(0); //Unsupported 
    }
  
  // Set all the rest of the option - KE: check what to shift to the part of SMT only
  decider->set_itp_bool_alg(options.get_unsigned_int_option("itp-algorithm"));
  decider->set_itp_euf_alg(options.get_unsigned_int_option("itp-uf-algorithm"));
  decider->set_itp_lra_alg(options.get_unsigned_int_option("itp-lra-algorithm"));
  if(options.get_option("itp-lra-factor").size() > 0) decider->set_itp_lra_factor(options.get_option("itp-lra-factor").c_str());
  decider->set_verbosity(options.get_unsigned_int_option("verbose-solver"));
  decider->set_certify(options.get_unsigned_int_option("check-itp"));
  if(options.get_bool_option("reduce-proof"))
  {
    decider->set_reduce_proof(options.get_bool_option("reduce-proof"));
    if(options.get_unsigned_int_option("reduce-proof-graph")) decider->set_reduce_proof_graph(options.get_unsigned_int_option("reduce-proof-graph"));
    if(options.get_unsigned_int_option("reduce-proof-loops")) decider->set_reduce_proof_loops(options.get_unsigned_int_option("reduce-proof-loops"));
  }
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
    status() << ("ASSERTION IS TRIVIALLY TRUE");
    report_success();
    return true;
  }
  
  // TODO: need to split this class and create a version for prop and smt
  // Unless we wish to unify mechanism also for error_trace!
  if (options.get_option("logic") == "prop")
    return assertion_holds_prop(assertion, store_summaries_with_assertion);
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
  const bool no_smt_usage = (options.get_option("logic") == "prop");

  omega.set_initial_precision(assertion);
  const unsigned last_assertion_loc = omega.get_last_assertion_loc();
  const bool single_assertion_check = omega.is_single_assertion_check();

  std::vector<unsigned> ints;
  get_ints(ints, options.get_option("part-itp"));

  prop_partitioning_target_equationt equation(ns, summarization_context, false,
      store_summaries_with_assertion, get_coloring_mode(options.get_option("color-proof")), ints);

  summary_infot& summary_info = omega.get_summary_info();
  symex_assertion_sumt symex = symex_assertion_sumt(
            summarization_context, summary_info, ns, symbol_table,
            equation, message_handler, goto_program, last_assertion_loc,
            single_assertion_check, !no_slicing_option, !no_ce_option, 
            !no_smt_usage);

  setup_unwind(symex);

  prop_refiner_assertion_sumt refiner = prop_refiner_assertion_sumt(
              summarization_context, omega,
              get_refine_mode(options.get_option("refine-mode")),
              message_handler, last_assertion_loc, true);

  prop_assertion_sumt prop = prop_assertion_sumt(summarization_context,
          equation, message_handler, max_memory_used);
  unsigned count = 0;
  bool end = false;
  if(&message_handler!=NULL){
	  std::cout <<"";
  }

  std::auto_ptr<prop_conv_solvert> decider_prop;
  std::auto_ptr<interpolating_solvert> interpolator;
  while (!end)
  {
    count++;
    
    // Init the next iteration context
    {
        decider = (new satcheck_opensmt2t())->set_prop_conv_solver(
                (dynamic_cast<prop_conv_solvert *> (decider_prop.get())));

        interpolator.reset(decider);
        bv_pointerst *deciderp = new bv_pointerst(ns, *(dynamic_cast<satcheck_opensmt2t *> (decider)));
        deciderp->unbounded_array = bv_pointerst::U_AUTO;
        decider_prop.reset(deciderp);
    }
    
    end = (count == 1) ? symex.prepare_SSA(assertion) : symex.refine_SSA (assertion, refiner.get_refined_functions());

    if (!end){
      if (options.get_bool_option("claims-opt") && count == 1){
        prop_dependency_checkert(ns, message_handler, goto_program, omega, options.get_unsigned_int_option("claims-opt"), equation.SSA_steps.size())
                .do_it(equation);
        status() << (std::string("Ignored SSA steps after dependency checker: ") + std::to_string(equation.count_ignored_SSA_steps()));
      }

      end = prop.assertion_holds(assertion, ns, *(dynamic_cast<prop_conv_solvert *> (decider_prop.get())), *(interpolator.get())); // KE: strange conversion after shift to cbmc 5.5 - I think the bv_pointerst is changed
      unsigned summaries_count = omega.get_summaries_count();
      unsigned nondet_count = omega.get_nondets_count();
      if (end && interpolator->can_interpolate())
      {
        if (options.get_bool_option("no-itp")){
          status() << ("Skip generating interpolants");
        } else {
          status() << ("Start generating interpolants...");
          extract_interpolants_prop(prop, equation, decider_prop, interpolator);
        }
        if (summaries_count == 0)
        {
          status() << ("ASSERTION(S) HOLD(S)"); //TODO change the message to something more clear (like, everything was inlined...)
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
            status() << ("A real bug found.") << endl << endl;
            report_failure();
            break;
          } else {
            //status("Counterexample is spurious");
            status() << ("Go to next iteration") << endl;
          }
        } else {
          prop.error_trace(*decider_prop, ns);
          status() << ("ASSERTION(S) DO(ES)N'T HOLD") << endl;
          status() << ("A real bug found") << endl << endl;
          report_failure();
          break;
        }
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
  return end;
}

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
  initial=current_time();
  
  const bool no_slicing_option = options.get_bool_option("no-slicing");
  const bool no_ce_option = options.get_bool_option("no-error-trace");
  const bool no_smt_usage = (options.get_option("logic") == "prop");

  omega.set_initial_precision(assertion);
  const unsigned last_assertion_loc = omega.get_last_assertion_loc();
  const bool single_assertion_check = omega.is_single_assertion_check();

  std::vector<unsigned> ints;
  get_ints(ints, options.get_option("part-itp"));

  smt_partitioning_target_equationt equation(ns, summarization_context, false,
      store_summaries_with_assertion, get_coloring_mode(options.get_option("color-proof")), ints);

  summary_infot& summary_info = omega.get_summary_info();
  symex_assertion_sumt symex = symex_assertion_sumt(
            summarization_context, summary_info, ns, symbol_table,
            equation, message_handler, goto_program, last_assertion_loc,
            single_assertion_check, !no_slicing_option, !no_ce_option,
            !no_smt_usage);

  setup_unwind(symex);

  smt_refiner_assertion_sumt refiner = smt_refiner_assertion_sumt(
              summarization_context, omega,
              get_refine_mode(options.get_option("refine-mode")),
              message_handler, last_assertion_loc, true);

  smt_assertion_sumt prop = smt_assertion_sumt(summarization_context,
          equation, message_handler, max_memory_used);
  unsigned count = 0;
  bool end = false;
  if(&message_handler!=NULL){
	  std::cout <<"";
  }

  while (!end)
  {
    count++;
    end = (count == 1) ? symex.prepare_SSA(assertion) : symex.refine_SSA (assertion, refiner.get_refined_functions());

    //LA: good place?
    if(options.get_bool_option("list-templates"))
    {
        cout << "Listing templates\n" << endl;
        list_templates(prop, equation);
        return true;
    }

    if (!end){
      if (options.get_bool_option("claims-opt") && count == 1){
        smt_dependency_checkert(ns, message_handler, goto_program, omega, options.get_unsigned_int_option("claims-opt"), equation.SSA_steps.size())
                .do_it(equation);
        status() << (std::string("Ignored SSA steps after dependency checker: ") + std::to_string(equation.count_ignored_SSA_steps()));
      }

      end = prop.assertion_holds(assertion, ns, 
              *(dynamic_cast<smtcheck_opensmt2t *> (decider)), 
              *(dynamic_cast<interpolating_solvert *> (decider)));
      unsigned summaries_count = omega.get_summaries_count();
      unsigned nondet_count = omega.get_nondets_count();
      if (end && decider->can_interpolate())
      {
        if (options.get_bool_option("no-itp")){
          status() << ("Skip generating interpolants") << endl;
        } else {
          status() << ("Start generating interpolants...") << endl;
          extract_interpolants_smt(prop, equation);
        }
        if (summaries_count == 0)
        {
          status() << ("ASSERTION(S) HOLD(S)"); //TODO change the message to something more clear (like, everything was inlined...)
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
          refiner.refine(*(dynamic_cast <smtcheck_opensmt2t*> (decider)), omega.get_summary_info(), equation);

          if (refiner.get_refined_functions().size() == 0){
            assertion_violated(prop, symex.guard_expln);
            break;
          } else {
            //status("Counterexample is spurious");
            status() << ("Go to next iteration") << endl;
          }
        } else {
          assertion_violated(prop, symex.guard_expln);
          break;
        }
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
  return end;
}

/*******************************************************************

 Function: summarizing_checkert::assertion_violated

 Inputs:

 Outputs:

 Purpose: Prints the error trace for smt encoding

\*******************************************************************/
void summarizing_checkert::assertion_violated (smt_assertion_sumt& prop,
				std::map<irep_idt, std::string> &guard_expln)
{
    smtcheck_opensmt2t* decider_smt = dynamic_cast <smtcheck_opensmt2t*> (decider);

    if (!options.get_bool_option("no-error-trace"))
        prop.error_trace(*decider_smt, ns, guard_expln);
    if (decider_smt->has_unsupported_vars()){
    	status() << "\nA bug found." << endl;
    	status() << "WARNING: Possibly due to the Theory conversion." << endl;
    } else {
    	status() << "A real bug found." << endl;
    }
    report_failure();

    decider_smt = NULL;
}

// Only for SMT version
void summarizing_checkert::list_templates(smt_assertion_sumt& prop, smt_partitioning_target_equationt& equation)
{
    summary_storet* summary_store = summarization_context.get_summary_store();
    vector<summaryt*> templates;
    smtcheck_opensmt2t* decider_smt = dynamic_cast <smtcheck_opensmt2t*> (decider);
    equation.fill_function_templates(*decider_smt, templates);
    decider_smt = NULL;
    for(unsigned int i = 0; i < templates.size(); ++i)
        summary_store->insert_summary(*templates[i]);
    // Store the summaries
    const std::string& summary_file = options.get_option("save-summaries");
    if (!summary_file.empty()) {
        summarization_context.serialize_infos_smt(summary_file, 
            omega.get_summary_info());
    }
}

/*******************************************************************\

Function: summarizing_checkert::extract_interpolants_smt

  Inputs:

 Outputs:

 Purpose: Extract and store the interpolation summaries for smt only

\*******************************************************************/
void summarizing_checkert::extract_interpolants_smt (smt_assertion_sumt& prop, smt_partitioning_target_equationt& equation)
{
  summary_storet* summary_store = summarization_context.get_summary_store();
  interpolant_mapt itp_map;
  absolute_timet before, after;
  before=current_time();
  
  smtcheck_opensmt2t* decider_smt = dynamic_cast <smtcheck_opensmt2t*> (decider);
  equation.extract_interpolants(*decider_smt, *decider_smt, itp_map);
  decider_smt = NULL;

  after=current_time();
  status() << "INTERPOLATION TIME: " << (after-before) << eom;

  for (interpolant_mapt::iterator it = itp_map.begin();
                  it != itp_map.end(); ++it) {
    summary_infot& summary_info = it->first->summary_info;

    function_infot& function_info =
            summarization_context.get_function_info(
            summary_info.get_function_id());

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
            std::auto_ptr<prop_conv_solvert> decider_prop, std::auto_ptr<interpolating_solvert> interpolator)
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

/*******************************************************************\

Function: summarizing_checkert::setup_unwind

  Inputs:

 Outputs:

 Purpose: Setup the unwind bounds.

\*******************************************************************/

void summarizing_checkert::setup_unwind(symex_assertion_sumt& symex)
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
    return FORCE_INLINING;
  } else if (str == "random-substitution" || str == "1"){
    return RANDOM_SUBSTITUTION;
  } else if (str == "slicing-result" || str == "2"){
    return SLICING_RESULT;
  } else {
    // by default
    return SLICING_RESULT;
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
    return ALL_HAVOCING;
  } else if (str == "use-summaries" || str == "1"){
    return ALL_SUBSTITUTING;
  } else {
    // by default
    return ALL_SUBSTITUTING;
  }
};


coloring_modet get_coloring_mode(const std::string& str)
{
  if (str == "0"){
    return RANDOM_COLORING;
  } else if (str == "1"){
    return COLORING_FROM_FILE;
  } else {
    // by default
    return NO_COLORING;
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
  //status() << ("VERIFICATION SUCCESSFUL");

  switch(message_handler.get_ui())
  {
  
  case ui_message_handlert::PLAIN:
	std::cout << std::endl << std::endl << "VERIFICATION SUCCESSFUL" << std::endl;
	break;

  case ui_message_handlert::XML_UI:
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

  case ui_message_handlert::PLAIN:
	std::cout << std::endl << std::endl << "VERIFICATION FAILED" << std::endl;
	break;

  case ui_message_handlert::XML_UI:
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
