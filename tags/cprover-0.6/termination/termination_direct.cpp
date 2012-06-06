/*******************************************************************\

Module: Direct termination engine (Biere et al.)

Author: CM Wintersteiger

\*******************************************************************/

#include <sstream>
#include <memory>

#include <i2string.h>

#include <satabs/prepare/prepare.h>
#include <satabs/refiner/select_refiner.h>
#include <satabs/abstractor/select_abstractor.h>
#include <satabs/modelchecker/select_modelchecker.h>
#include <satabs/simulator/select_simulator.h>
#include <satabs/satabs_safety_checker.h>

#include "termination_direct.h"

#include "termination_slicer.h"

/********************************************************************\

 Function: termination_directt::terminates

 Inputs:

 Outputs:

 Purpose: Perform Termination Check for one specific loop

\********************************************************************/

termination_resultt termination_directt::terminates(
  const irep_idt &main,
  const goto_functionst &goto_functions,
  goto_programt::const_targett assertion)
{    
  goto_programt::targett sliced_assertion;
  
  fine_timet before=current_time();
   
  goto_functionst dest_func;
  int mres=sliced_abstraction(context,
                              shadow_context,
                              goto_functions,
                              main,
                              assertion,
                              sliced_assertion,
                              dest_func,
                              get_message_handler());
  
  concrete_modelt model(ns, dest_func);
  
  slicing_time+=current_time()-before;
    
  if(!mres)
  {
    status("Slicer has shown unreachability of the assertion.");      
    return T_TERMINATING;
  }
    
  /*
  if(cmdline.isset("no-value-sets"))
    model.value_set_analysis.initialize(model.goto_functions);
  else
  {
    status("Pointer analysis...");  
    fine_timet before=current_time();
    model.value_set_analysis(model.goto_functions);  
    pointer_analysis_time=current_time()-before;
  }
  */
  
  nul_message_handlert nmh;
  message_handlert & mh = (verbosity >= 8) ? get_message_handler() : nmh;
  loop_componentt::argst args(get_message_handler(), model);

  std::auto_ptr<refinert> refiner(select_refiner(cmdline, args));
  std::auto_ptr<abstractort> abstractor(select_abstractor(cmdline, args));
  std::auto_ptr<modelcheckert> modelchecker(select_modelchecker(cmdline, args));
  std::auto_ptr<simulatort> simulator(select_simulator(cmdline, args, 
                                                       shadow_context));
  
  unsigned this_verb=verbosity-2;
  
  // set their verbosity -- all the same for now
  refiner->set_verbosity(this_verb);
  abstractor->set_verbosity(this_verb);
  modelchecker->set_verbosity(this_verb);
  simulator->set_verbosity(this_verb);    
  
  #if 0
  std::string fname("model_"); 
  fname += i2string(call_counter);
  std::ofstream out(fname.c_str());
  model.goto_functions.output(ns, out);
  out.close();  
  #endif
      
  
  satabs_safety_checkert safety_checker(ns, *abstractor, *refiner, *modelchecker, *simulator);
  safety_checker.set_message_handler(mh);
  safety_checker.set_verbosity(this_verb);
                 
  status("Running CEGAR...");
  
  try {
    #if 0
    std::string fname="model_" + i2string(call_counter) + "_" + i2string(++cnt) + ".bin";
    out.open(fname.c_str());
    write_goto_binary(out, context, model.goto_functions);
    out.close();
    #endif
      
    fine_timet before=current_time();
    safety_checkert::resultt result=safety_checker(model.goto_functions);
    fine_timet time_diff=current_time()-before;
    modelchecker_time+=time_diff;
          
    switch(result)
    {
      case safety_checkert::ERROR: throw ("CEGAR Error");
      
      case safety_checkert::UNSAFE:
        counter_example_extraction_time+=time_diff;
        return T_NONTERMINATING;
        break;
  
      case safety_checkert::SAFE:
        final_check_time+=time_diff;        
        return T_TERMINATING;
  
      default:
        throw (std::string("CEGAR Result: ") + i2string(result));
    }
  }
  catch (const std::string &s)
  {
    status(std::string("CEGAR Loop Exception: ") + s);
  }
  catch (const char *s)
  {
    status(std::string("CEGAR Loop Exception: ") + s);
  }
  catch (unsigned u)
  {
    status(std::string("CEGAR Loop Exception: ") + i2string(u));
  }
  
  return T_NONTERMINATING;
}

/********************************************************************\

 Function: termination_directt::terminates

 Inputs:

 Outputs:

 Purpose: Perform Termination Check for all loops at the same time

\********************************************************************/

termination_resultt termination_directt::terminates(
  const goto_functionst &goto_functions)
{  
  concrete_modelt model(ns, goto_functions);
  
  /*
  if(cmdline.isset("no-value-sets"))
    model.value_set_analysis.initialize(model.goto_functions);
  else
  {
    status("Pointer analysis...");  
    fine_timet before=current_time();
    model.value_set_analysis(model.goto_functions);  
    pointer_analysis_time=current_time()-before;
  }
  */
    
  nul_message_handlert nmh;
  message_handlert & mh = (verbosity >= 8) ? get_message_handler() : nmh;
  loop_componentt::argst args(get_message_handler(), model);  

  // finds predicates
  std::auto_ptr<refinert> refiner(
    select_refiner(cmdline, args));

  // calculates abstract program
  std::auto_ptr<abstractort> abstractor(
    select_abstractor(cmdline, args));

  // model checking engine
  std::auto_ptr<modelcheckert> modelchecker(
    select_modelchecker(cmdline, args));

  // simulator
  std::auto_ptr<simulatort> simulator(
    select_simulator(cmdline, args, shadow_context));
  
  unsigned this_verb=verbosity-2;
  
  // set their verbosity -- all the same for now
  refiner->set_verbosity(this_verb);
  abstractor->set_verbosity(this_verb);
  modelchecker->set_verbosity(this_verb);
  simulator->set_verbosity(this_verb);    
  
  #if 0
  std::ofstream out("model");
  model.goto_functions.output(ns, out);
  out.close();
  #endif
  
  satabs_safety_checkert safety_checker(ns, *abstractor, *refiner, *modelchecker, *simulator);
  safety_checker.set_message_handler(mh);
  safety_checker.set_verbosity(this_verb);
               
  status("Running CEGAR...");
  
  try {
    switch(safety_checkert::resultt result=safety_checker(model.goto_functions))
    {
      case safety_checkert::ERROR: throw ("CEGAR Error");
  
      case safety_checkert::UNSAFE:
        return T_NONTERMINATING;
      
      case safety_checkert::SAFE:
        return T_TERMINATING;
  
      default:
        throw (std::string("CEGAR Result: ") + i2string(result));      
    } 
  }
  catch (const std::string &s)
  {
    status(std::string("CEGAR Loop Exception: ") + s);
  }
  catch (const char *s)
  {
    status(std::string("CEGAR Loop Exception: ") + s);
  }
  catch (unsigned u)
  {
    status(std::string("CEGAR Loop Exception: ") + i2string(u));
  }

  return T_NONTERMINATING;
}

/********************************************************************\

 Function: termination_directt::operator()

 Inputs:

 Outputs:

 Purpose: Binary Reachability termination checks 

\********************************************************************/

termination_resultt termination_directt::operator()()
{
  // Precondition: program must be termination-instrumented
  
  irep_idt main=(cmdline.isset("function"))? cmdline.getval("function") : 
                                             "main";
  goto_functionst::function_mapt::const_iterator mit=
      goto_functions.function_map.find(main);
  
  if(mit==goto_functions.function_map.end() ||
     !mit->second.body_available)
  {
    error("Entry point not found.");
    return T_ERROR;
  }
  

  if(cmdline.isset("no-loop-slicing"))
  {
    forall_goto_functions(it, goto_functions)
      forall_goto_program_instructions(iit, it->second.body)
        if(iit->is_assert()) 
          total_loops++;
    
    if(terminates(goto_functions)!=T_TERMINATING)
      nonterminating_loops++;
  }
  else
  {
    const goto_programt &prog=mit->second.body;
    goto_programt::const_targett entry=prog.instructions.begin();
    std::list<goto_programt::const_targett> recstack;
    
    // this returns a loop multiple times, if it appears on multiple
    // callpaths. There is no need to re-check those, as all callpaths
    // are taken into account by the slicer.
    goto_programt::const_targett assertion=find_next_loop(entry, prog, recstack);
    
    std::set<goto_programt::const_targett> seen_loops;
  
    while(assertion!=prog.instructions.end())
    {    
      if(seen_loops.find(assertion)==seen_loops.end())
      {
        total_loops++;        
        const locationt &loc=assertion->location;
        
        status("==================================================");
        status("Loop Termination Check #" + i2string(total_loops));
        status(std::string("at: ") + ((loc.is_nil()) ? "?" : loc.as_string()));
        status("--------------------------------------------------");
        
        if(!assertion->guard.is_true())
        {
          fine_timet time=current_time();
          termination_resultt res=terminates(main, goto_functions, assertion);
          time=current_time()-time;
          
          status("Check Time: " + time2string(time) + " s");
          
          if(res!=T_TERMINATING)
          {
            status("LOOP DOES NOT TERMINATE");
            nonterminating_loops++;
          }
          else
            status("LOOP TERMINATES");
        }
                
        status("==================================================");
        
        seen_loops.insert(assertion);
      }
      
      assertion = find_next_loop(assertion, prog, recstack);
    }
    
    assert(recstack.empty());
  }
    
  if(nonterminating_loops>0)
  {
    status("Program is (possibly) NON-TERMINATING.");
    return T_NONTERMINATING;
  }
  else
  {
    status("Program TERMINATES.");
    return T_TERMINATING;
  }
}

/********************************************************************\

 Function: termination_directt::show_stats()

 Inputs:

 Outputs:

 Purpose:  

\********************************************************************/

void termination_directt::show_stats(void)
{
  std::stringstream ss;      
    
  ss << "Pointer analysis: " <<
    time2string(pointer_analysis_time) << " s total.";  
    
  status(ss.str());
  ss.clear();
    
  ss << "Loop slicer: " <<
    time2string(slicing_time) << " s total.";  
      
  status(ss.str());
  
  termination_baset::show_stats();
}
