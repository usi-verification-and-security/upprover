/*******************************************************************\  
 
Module: CEGAR Loop

Author: Daniel Kroening
        Karen Yorav 

Date: June 2003

\*******************************************************************/

#include <sstream>

#include <i2string.h>

#include <goto-symex/xml_goto_trace.h>

#include "abstractor/initial_abstraction.h"
#include "modelchecker/modelchecker_boolean_program.h"
#include "cegar_loop.h"
#include "status_values.h"

/*******************************************************************\

Function: cegar_loopt::show_statistics

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cegar_loopt::show_statistics()
{
  {
    std::ostringstream str;
    str << "Time: ";
    output_time(total_time, str);
    str << " total, ";
    output_time(abstractor_time, str);
    str << " abstractor, ";
    output_time(modelchecker_time, str);
    str << " model checker, ";
    output_time(simulator_time, str);
    str << " simulator, ";
    output_time(refiner_time, str);
    str << " refiner";
    status(str.str());
  }
  
  {
    std::ostringstream str;
    str << "Iterations: " << iteration;
    status(str.str());
  }
  
  {
    std::ostringstream str;
    str << "Predicates: " << predicates.size();
    status(str.str());
  }
  
}

/*******************************************************************\

Function: cegar_loopt::show_counterexample

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cegar_loopt::show_counterexample(
  const concrete_counterexamplet &concrete_counterexample)
{
  switch(ui)
  {
  case ui_message_handlert::OLD_GUI:
    show_counterexample_gui(std::cout, context, concrete_counterexample);
    break;
    
  case ui_message_handlert::XML_UI:
    {
      xmlt xml;
      namespacet ns(context, shadow_context);
      convert(ns, concrete_counterexample.goto_trace, xml);
      std::cout << xml << std::endl;
    }
    break;

  case ui_message_handlert::PLAIN:
    result("Counterexample:");
    ::show_counterexample(std::cout, context, concrete_counterexample);
    break;
  
  default:
    assert(false);
  }
}

/*******************************************************************\

Function: cegar_loopt::do_abstraction

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cegar_loopt::do_abstraction()
{
  fine_timet start_time=current_time();

  abstractor.build_abstraction(predicates);

  abstractor_time+=current_time()-start_time;
}

/*******************************************************************\

Function: cegar_loopt::do_modelchecking

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool cegar_loopt::do_modelchecking(
  abstract_counterexamplet &abstract_counterexample)
{
  // do we want to save Boolean programs?
  if(save_bps)
  {
    namespacet ns(context);
    modelchecker_boolean_programt model_checker_boolean_program(
      loop_componentt::argst(get_message_handler(), concrete_model),
      modelchecker_boolean_programt::BOPPO, 0);
    model_checker_boolean_program.save(
      abstractor.abstract_model,
      iteration);
  }

  fine_timet start_time=current_time();

  bool pass=
    modelchecker.check(abstractor.abstract_model,
                       abstract_counterexample); 

  modelchecker_time+=current_time()-start_time;
  
  return pass;
}

/*******************************************************************\

Function: cegar_loopt::do_simulation

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool cegar_loopt::do_simulation(
  abstract_counterexamplet &abstract_counterexample,
  concrete_counterexamplet &concrete_counterexample,
  fail_infot &fail_info)
{
  fine_timet start_time=current_time();
  
  // Check the counterexample
  bool is_spurious=simulator.is_spurious(
    predicates,
    abstractor.abstract_model,
    abstract_counterexample,
    concrete_counterexample,
    fail_info);

  simulator_time+=current_time()-start_time;
    
  return is_spurious;
}

/*******************************************************************\

Function: cegar_loopt::do_refinement

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cegar_loopt::do_refinement(
  const abstract_counterexamplet &abstract_counterexample,
  fail_infot &fail_info)
{
  fine_timet start_time=current_time();

  refiner.refine(
     predicates,
     abstractor.abstract_model,
     fail_info);

  refiner_time+=current_time()-start_time;
}

/*******************************************************************\

Function: cegar_loopt::report_failure

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cegar_loopt::report_failure()
{
  result("VERIFICATION FAILED");

  switch(ui)
  {
  case ui_message_handlert::OLD_GUI:
    break;
    
  case ui_message_handlert::XML_UI:
    {
      xmlt xml("cprover-status");
      xml.data="FAILURE";
      std::cout << xml;
      std::cout << std::endl;
    }
    break;
    
  default:;
  }
}

/*******************************************************************\

Function: cegar_loopt::report_success

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cegar_loopt::report_success()
{
  result("VERIFICATION SUCCESSFUL");

  switch(ui)
  {
  case ui_message_handlert::OLD_GUI:
    break;
    
  case ui_message_handlert::XML_UI:
    {
      xmlt xml("cprover-status");
      xml.data="SUCCESS";
      std::cout << xml;
      std::cout << std::endl;
    }
    break;
    
  default:;
  }
}                       

/*******************************************************************\

Function: cegar_loopt::go

  Inputs:

 Outputs:

 Purpose: execute the CEGAR loop

\*******************************************************************/

int cegar_loopt::go()
{
  status("*** Starting CEGAR Loop ***");

  int result=CEGAR_ERROR;
  fine_timet start_time=current_time();
  abstractor_time=0;
  modelchecker_time=0;
  simulator_time=0;
  refiner_time=0;
  iteration=0;

  {
    // Create initial abstraction
    
    initial_abstractiont initial_abstraction(get_message_handler());
    initial_abstraction.set_verbosity(get_verbosity());
    
    initial_abstraction.build(concrete_model, abstractor.abstract_model);
    
    if(initial_predicates.empty())
      initial_abstraction.init_preds(context, predicates, concrete_model);
    else
      initial_abstraction.init_preds(
        context, predicates, initial_predicates, abstractor.abstract_model);
  }

  while(true) 
  {
    iteration++;

    status("*** CEGAR Loop Iteration "+i2string(iteration));

    do_abstraction();

    // abstract counterexample 
    abstract_counterexamplet abstract_counterexample;

    // does the spec hold? 
    if(do_modelchecking(abstract_counterexample))
    {
      report_success();
      result=CEGAR_PROPERTY_HOLDS;
      break;
    }
    else
    { 
      fail_infot fail_info;
      
      // Check the counterexample
      if(do_simulation(
        abstract_counterexample,
        concrete_counterexample,
        fail_info))
      {
        status("Trace is spurious");

        if(iteration==max_iterations)
        {
          error("Too many iterations, giving up.");
          error("Consider increasing the number of iterations.");
          result=CEGAR_ITERATIONS;
          break;
        }

        // it is spurious, refine
        do_refinement(abstract_counterexample, fail_info);
      }
      else
      {
        // counterexample is not spurious

        // show it nicely
        show_counterexample(concrete_counterexample);
        report_failure();
        result=CEGAR_COUNTEREXAMPLE;
        break;
      }
    }
  }

  total_time=current_time()-start_time;
  show_statistics();
  
  return result;
}

/*******************************************************************\

Function: cegar_loopt::re_abstract

  Inputs:

 Outputs:

 Purpose: mark an instruction for re-abstraction

\*******************************************************************/

void cegar_loopt::re_abstract(const goto_programt::const_targett target)
{
  abstract_functionst &afuncs=abstractor.abstract_model.goto_functions;
  for(abstract_functionst::function_mapt::iterator it=
        afuncs.function_map.begin();
      it!=afuncs.function_map.end();
      it++)
  {
    for(abstract_programt::instructionst::iterator iit=
          it->second.body.instructions.begin();
        iit!=it->second.body.instructions.end();
        iit++)    
    {
      if(iit->code.concrete_pc==target)
      {
        iit->code.re_abstract=true;
        return;
      }
    }
  }
}  
