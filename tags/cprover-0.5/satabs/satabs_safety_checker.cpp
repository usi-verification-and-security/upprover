/*******************************************************************\

Module: Safety Checker Interface

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <sstream>

#include <i2string.h>

#include "abstractor/initial_abstraction.h"
#include "modelchecker/modelchecker_boolean_program.h"
#include "satabs_safety_checker.h"

/*******************************************************************\

Function: satabs_safety_checkert::satabs_safety_checkert

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

satabs_safety_checkert::satabs_safety_checkert(
  const namespacet &_ns,
  abstractort &_abstractor,
  refinert &_refiner,
  modelcheckert &_modelchecker,
  simulatort &_simulator):
  safety_checkert(_ns),
  max_iterations(0),
  save_bps(false),
  abstractor(_abstractor),
  refiner(_refiner),
  modelchecker(_modelchecker),
  simulator(_simulator)
{
}

/*******************************************************************\

Function: satabs_safety_checkert::show_statistics

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void satabs_safety_checkert::show_statistics()
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

Function: satabs_safety_checkert::do_abstraction

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void satabs_safety_checkert::do_abstraction()
{
  fine_timet start_time=current_time();

  abstractor.build_abstraction(predicates);

  abstractor_time+=current_time()-start_time;
}

/*******************************************************************\

Function: satabs_safety_checkert::do_modelchecking

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool satabs_safety_checkert::do_modelchecking(
  const concrete_modelt &concrete_model,
  abstract_counterexamplet &abstract_counterexample)
{
  // do we want to save Boolean programs?
  if(save_bps)
  {
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

Function: satabs_safety_checkert::do_simulation

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool satabs_safety_checkert::do_simulation(
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

Function: satabs_safety_checkert::do_refinement

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void satabs_safety_checkert::do_refinement(
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

Function: satabs_safety_checkert::operator()

  Inputs:

 Outputs:

 Purpose: execute the CEGAR loop

\*******************************************************************/

safety_checkert::resultt satabs_safety_checkert::operator()(
  const goto_functionst &goto_functions)
{
  status("*** Starting CEGAR Loop ***");

  resultt result=ERROR;
  fine_timet start_time=current_time();
  abstractor_time=0;
  modelchecker_time=0;
  simulator_time=0;
  refiner_time=0;
  iteration=0;
  
  concrete_modelt concrete_model(ns, goto_functions);

  {
    // Create initial abstraction
    
    initial_abstractiont initial_abstraction(get_message_handler());
    initial_abstraction.set_verbosity(get_verbosity());
    
    initial_abstraction.build(concrete_model, abstractor.abstract_model);
    
    if(initial_predicates.empty())
      initial_abstraction.init_preds(ns, predicates, concrete_model);
    else
      initial_abstraction.init_preds(
        ns, predicates, initial_predicates, abstractor.abstract_model);
  }

  while(true) 
  {
    iteration++;

    status("*** CEGAR Loop Iteration "+i2string(iteration));

    do_abstraction();

    // abstract counterexample 
    abstract_counterexamplet abstract_counterexample;

    // does the spec hold? 
    if(do_modelchecking(concrete_model, abstract_counterexample))
    {
      result=SAFE;
      break;
    }
    else
    { 
      fail_infot fail_info;
      concrete_counterexamplet concrete_counterexample;
      
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
          result=ERROR;
          break;
        }

        // it is spurious, refine
        do_refinement(abstract_counterexample, fail_info);
      }
      else
      {
        // counterexample is not spurious -- store it
        // as error trace
        error_trace.swap(concrete_counterexample.goto_trace);
        result=UNSAFE;
        break;
      }
    }
  }

  total_time=current_time()-start_time;
  show_statistics();
  
  return result;
}

/*******************************************************************\

Function: satabs_safety_checkert::re_abstract

  Inputs:

 Outputs:

 Purpose: mark an instruction for re-abstraction

\*******************************************************************/

void satabs_safety_checkert::re_abstract(const goto_programt::const_targett target)
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
