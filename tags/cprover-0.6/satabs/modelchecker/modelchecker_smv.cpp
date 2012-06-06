/*******************************************************************\

Module: SMV Model Checker Interface

Author: Daniel Kroening

  Date: June 2003

\*******************************************************************/

#include <assert.h>
#include <stdlib.h>
#include <ctype.h>
#include <stdio.h>

#include <fstream>
#include <list>
#include <algorithm>

#include <str_getline.h>
#include <i2string.h>
#include <prefix.h>
#include <smvlang/expr2smv.h>

#include "modelchecker_smv.h"

/*******************************************************************\

Function: modelchecker_smvt::smv_ce_thread_infot::build

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void modelchecker_smvt::smv_ce_thread_infot::build(
  const inlinedt &inlined,
  const threadt &thread)
{
  guards.resize(inlined.PC_map.size());
  t=&thread;
}

/*******************************************************************\

Function: modelchecker_smvt::read_result

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool modelchecker_smvt::read_result(
  std::istream &out1,
  std::istream &out2,
  std::istream &out_ce,
  abstract_modelt &abstract_model,
  const threadst &threads,
  abstract_counterexamplet &counterexample)
{
  // check for errors first
  
  {
    std::list<std::string> file;

    while(true)
    {
      std::string line;
      if(!str_getline(out2, line)) break;
      file.push_back(line);
    }

    if(!file.empty())
      throw "SMV error";
  }

  // now read output
  
  if(engine==CADENCE_SMV)
    return read_result_cadence_smv(
      out_ce,
      abstract_model,
      threads,
      counterexample);
  
  {
    std::list<std::string> file;

    while(true)
    {
      std::string line;
      if(!str_getline(out1, line)) break;
      file.push_back(line);
    }
    
    if(file.empty())
      throw "SMV error";

    for(std::list<std::string>::const_iterator 
        it=file.begin(); it!=file.end(); it++)
    {
      if(std::string(*it, 0, 16)=="-- specification")
      {
        if(std::string(*it, it->size()-7)=="is true")
        {
          // OK
        }
        else if(std::string(*it, it->size()-8)=="is false")
        {
          // produce counterexample
          status("SMV produced counterexample");
          read_counterexample(file, it, abstract_model,
                              threads, counterexample);
          print(9, "SMV counterexample sucessfully read\n");

          // show it
          //std::cout << counterexample;
          return false;
        }
        else
          throw "unexpected reply from SMV: \""+*it+"\"";
      }
    }
  }

  return true;
}

/*******************************************************************\

Function: modelchecker_smvt::read_result_cadence_smv

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool modelchecker_smvt::read_result_cadence_smv(
  std::istream &out_ce,
  abstract_modelt &abstract_model,
  const threadst &threads,
  abstract_counterexamplet &counterexample)
{
  std::list<std::string> file;

  while(true)
  {
    std::string line;
    if(!str_getline(out_ce, line)) break;
    file.push_back(line);
  }
  
  if(file.empty())
    throw "SMV error";

  for(std::list<std::string>::const_iterator 
      it=file.begin(); it!=file.end(); it++)
  {
    if(std::string(*it, 0, 18)=="/* truth value */ ")
    {
      if(std::string(*it, it->size()-1)=="1")
      {
        // OK
      }
      else if(std::string(*it, it->size()-1)=="0")
      {
        // produce counterexample
        status("Cadence SMV produced counterexample");
        read_counterexample_cadence_smv(
          file, it, abstract_model,
          threads, counterexample);
        print(9, "Cadence SMV counterexample sucessfully read");
        return false;
      }
      else
        throw "unexpected reply from Cadence SMV: \""+*it+"\"";
    }
  }

  return true;
}

/*******************************************************************\

Function: modelchecker_smvt::read_counterexample_store

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void modelchecker_smvt::read_counterexample_store(
  const abstract_modelt &abstract_model,
  abstract_counterexamplet &counterexample,
  thread_infost &thread_infos,
  abstract_stept &abstract_state)
{
  // end of state -- find out which thread was running
  unsigned thread_nr=0;

  if(thread_infos.size()>=2)
  {
    for(thread_nr=0; thread_nr<thread_infos.size(); thread_nr++)
      if(thread_infos[thread_nr].runs)
        break;

    if(thread_nr==thread_infos.size())
      throw "found no thread running";
  }

  abstract_state.thread_nr=thread_nr;
  abstract_state.branch_taken=true;

  smv_ce_thread_infot &thread_info=thread_infos[thread_nr];

  if(thread_info.PC<inlined.PC_map.size())
  {
    abstract_state.pc=inlined.PC_map[thread_info.PC].original;
    abstract_state.has_pc=true;

    if(abstract_state.pc->is_goto())
    {
      if(abstract_state.pc->guard.is_constant())
        abstract_state.branch_taken=abstract_state.pc->guard.is_true();
      else
        abstract_state.branch_taken=thread_info.guards[thread_info.PC];
    }
  }
  else
    abstract_state.has_pc=false;

  if(abstract_state.has_pc)
    counterexample.steps.push_back(abstract_state);
}

/*******************************************************************\

Function: modelchecker_smvt::read_counterexample

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void modelchecker_smvt::read_counterexample(
  const std::list<std::string> &file,
  std::list<std::string>::const_iterator it,
  abstract_modelt &abstract_model,
  const threadst &threads,
  abstract_counterexamplet &counterexample)
{
  while(it!=file.end() && 
        (std::string(*it, 0, 1)=="*" ||
         std::string(*it, 0, 1)=="-" ||
         std::string(*it, 0, 5)=="Trace"))
    it++;

  abstract_statet abstract_state;
  abstract_state.predicate_values.resize(
    abstract_model.variables.size());

  bool data_set=false;

  std::vector<smv_ce_thread_infot> thread_infos;
  thread_infos.resize(threads.size());

  {
    unsigned i=0;
    for(threadst::const_iterator t_it=threads.begin();
        t_it!=threads.end();
        t_it++, i++)
      thread_infos[i].build(inlined, *t_it);
  }

  for(; it!=file.end(); it++)
  {
    //std::cout << "Xx " << *it << "\n";

    if(std::string(*it, 0, 3)=="-- ")
      break;
    else if(*it=="resources used:")
      break;
    else if(std::string(*it, 0, 6)=="state " ||
            std::string(*it, 0, 10)=="-> State: " ||
            std::string(*it, 0, 10)=="-> Input: " ||
            *it=="")
    {
      if(!data_set) continue;

      read_counterexample_store(
        abstract_model, counterexample, thread_infos, abstract_state);

      data_set=false;
    }
    else
    {
      std::string::size_type p=it->find('=');

      if(p==std::string::npos)
        throw "unexpected line in counterexample: "+*it;

      std::string original_variable(*it, 0, p-1);
      std::string value(*it, p+2, std::string::npos);

      while(!original_variable.empty() &&
            original_variable[0]==' ')
        original_variable.erase(0, 1);

      std::string variable=original_variable;

      unsigned thread_nr=0;

      if(variable.empty())
        throw "failed to get variable name";
      else if(variable[0]=='t') // checked for emptyness above
      {
        thread_nr=atoi(variable.c_str()+1);

        std::string::size_type q=original_variable.find('.');

        if(q==std::string::npos)
          throw "unexpected line in counterexample: "+*it;

        variable=std::string(original_variable, q+1, std::string::npos);

        if(variable.empty())
          throw "failed to get sub-variable name from "+original_variable;
      }

      if(variable=="PC")
      {
        thread_infos[thread_nr].PC=atoi(value.c_str());
        data_set=true;
      }
      else if(variable=="runs")
      {
        thread_infos[thread_nr].runs=atoi(value.c_str());
        data_set=true;
      }
      else if(has_prefix(variable, "b"))
      {
        unsigned nr=atoi(variable.c_str()+1);
        if(nr>=abstract_state.predicate_values.size())
          throw "invalid variable in abstract counterexample: "+
            variable;

        abstract_state.predicate_values[nr]=atoi(value.c_str());
        data_set=true;
      }
      else if(has_prefix(variable, "guard"))
      {
        unsigned nr=atoi(variable.c_str()+5);
        if(nr>=thread_infos[thread_nr].guards.size())
          throw "invalid variable in abstract counterexample: "+
            variable;

        thread_infos[thread_nr].guards[nr]=atoi(value.c_str());
      }
      else if(has_prefix(variable, "nondet"))
      {
      }
      else if(has_prefix(variable, "start_thread_"))
      {
      }
      else if(variable=="end_thread")
      {
      }
      else if(variable=="started")
      {
      }
      else if(has_prefix(variable, "po_"))
      {
      }
      else if(variable=="atomic")
      {
      }
      else
        throw "unknown variable in abstract counterexample: "+
              original_variable+" (stripped: `"+variable+"')";
    }
  }

  if(data_set)
    read_counterexample_store(
      abstract_model, counterexample, thread_infos, abstract_state);
}

/*******************************************************************\

Function: modelchecker_smvt::read_counterexample_cadence_smv

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void modelchecker_smvt::read_counterexample_cadence_smv(
  const std::list<std::string> &file,
  std::list<std::string>::const_iterator it,
  abstract_modelt &abstract_model,
  const threadst &threads,
  abstract_counterexamplet &counterexample)
{
  while(it!=file.end() && *it!="{")
    it++;

  if(it==file.end())
    throw "unexpected end of counterexample";

  it++;

  std::vector<smv_ce_thread_infot> thread_infos;
  thread_infos.resize(threads.size());

  {
    unsigned i=0;
    for(threadst::const_iterator t_it=threads.begin();
        t_it!=threads.end();
        t_it++, i++)
      thread_infos[i].build(inlined, *t_it);
  }

  for(; it!=file.end(); it++)
  {
    if(*it=="}")
      break; // done with the trace

    if(std::string(*it, 0, 8)!="/* state")
      throw "expected state in counterexample, but got "+*it;
      
    abstract_statet abstract_state;
    abstract_state.predicate_values.resize(
      abstract_model.variables.size());

    it++;
    if(it==file.end())
      throw "unexpected end of counterexample";

    for(; it!=file.end(); it++)
    {
      if(std::string(*it, 0, 1)=="#")
      {
        // ignore
      }
      else if(*it=="}")
      {
        // done with the state
        read_counterexample_store(
          abstract_model, counterexample, thread_infos, abstract_state);
        break;
      }
      else
      {
        std::string::size_type p=it->find('=');

        if(p==std::string::npos)
          throw "unexpected line in counterexample: "+*it;

        std::string original_variable(*it, 0, p-1);
        std::string value(*it, p+2, std::string::npos);

        while(!original_variable.empty() &&
              original_variable[0]==' ')
          original_variable.erase(0, 1);

        while(!original_variable.empty() &&
              original_variable[original_variable.size()-1]==' ')
          original_variable.erase(original_variable.size()-1, std::string::npos);

        std::string variable=original_variable;

        if(!variable.empty() && variable[0]=='\\')
          variable.erase(0, 1);

        unsigned thread_nr=0;

        if(variable.empty())
          throw "failed to get variable name";
        else if(variable[0]=='t') // checked for emptyness above
        {
          thread_nr=atoi(variable.c_str()+1);

          std::string::size_type q=original_variable.find('.');

          if(q==std::string::npos)
            throw "unexpected line in counterexample: "+*it;

          variable=std::string(original_variable, q+1, std::string::npos);

          if(!variable.empty() && variable[0]=='\\')
            variable.erase(0, 1);

          if(variable.empty())
            throw "failed to get sub-variable name from "+original_variable;
        }

        if(variable=="PC")
          thread_infos[thread_nr].PC=atoi(value.c_str());
        else if(variable=="runs")
          thread_infos[thread_nr].runs=atoi(value.c_str());
        else if(has_prefix(variable, "b"))
        {
          unsigned nr=atoi(variable.c_str()+1);
          if(nr>=abstract_state.predicate_values.size())
            throw "invalid variable in abstract counterexample: "+
              variable;

          abstract_state.predicate_values[nr]=atoi(value.c_str());
        }
        else if(has_prefix(variable, "guard"))
        {
          unsigned nr=atoi(variable.c_str()+5);
          if(nr>=thread_infos[thread_nr].guards.size())
            throw "invalid variable in abstract counterexample: "+
              variable;

          thread_infos[thread_nr].guards[nr]=atoi(value.c_str());
        }
        else if(has_prefix(variable, "nondet"))
        {
        }
        else if(has_prefix(variable, "start_thread_"))
        {
        }
        else if(variable=="end_thread")
        {
        }
        else if(variable=="started")
        {
        }
        else if(has_prefix(variable, "po_"))
        {
        }
        else if(variable=="atomic")
        {
        }
        else
          throw "unknown variable in abstract counterexample: "+
                original_variable+" (stripped: "+variable+")";
      }
    }
  }
  
  //std::cout << counterexample << std::endl;
}

/*******************************************************************\

Function: modelchecker_smvt::build_smv_file

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void modelchecker_smvt::build_smv_file(
  const abstract_modelt &abstract_model,
  const threadst &threads,
  std::ostream &out)
{
  // start printing SMV

  out << "-- automatically generated by CPROVER/SATABS\n"
         "\n";
         
  out << "-- threads: " << threads.size() << std::endl
      << std::endl;

  if(threads.size()==1)
  {
    threaded=false;

    out << "MODULE main\n"
           "\n";

    build_smv_file_global_variables(abstract_model, out);

    build_smv_file(abstract_model, out);
  }
  else
  {
    threaded=true;

    out << "MODULE main\n"
           "\n";

    build_smv_file_global_variables(abstract_model, out);

    {
      unsigned thread_nr=0;

      for(threadst::const_iterator t_it=threads.begin();
          t_it!=threads.end();
          t_it++, thread_nr++)
      {
        out << "VAR t" << thread_nr << ": thread(";
        
        // initial PC
        
        out << t_it->initial_PC;

        // the predicates

        for(unsigned i=0;
            i<abstract_model.variables.size();
            i++)
          out << ", " << variable_names[i];

        out << ");" << std::endl;
      }
    }

    out << std::endl;
    
    out << "-- atomic sections" << std::endl;
    
    out << "VAR atomic: boolean;" << std::endl << std::endl;
    
    out << "ASSIGN init(atomic):=0;" << std::endl << std::endl;
    out << "ASSIGN next(atomic):=case" << std::endl;

    for(unsigned thread_nr=0; thread_nr<threads.size(); thread_nr++)
    {
      bool has_atomic=false;
      for(unsigned PC=0; PC<inlined.PC_map.size(); PC++)
        if(inlined.PC_map[PC].original->is_atomic_begin())
          has_atomic=true;

      out << "    t" << thread_nr << ".runs: ";
      
      if(has_atomic)
      {
        out << "case";

        for(unsigned PC=0; PC<inlined.PC_map.size(); PC++)
        {
          if(inlined.PC_map[PC].original->is_atomic_begin())
            out << " t" << thread_nr << ".PC=" << PC << ": 1;";
          else if(inlined.PC_map[PC].original->is_atomic_end())
            out << " t" << thread_nr << ".PC=" << PC << ": 0;";
        }
        
        out << " 1: atomic; esac;";
      }
      else
        out << "atomic; -- thread has no atomic section";
      
      out << std::endl;
    }
    
    out << "  esac;" << std::endl;

    out << std::endl;

    for(unsigned thread_nr=0; thread_nr<threads.size(); thread_nr++)
    {
      out << "TRANS (t" << thread_nr << ".runs & next(atomic))->next(t"
          << thread_nr << ".runs)" << std::endl;
    }    

    out << std::endl;

    out << "-- thread startup" << std::endl;

    out << std::endl;

    for(unsigned thread_nr=0; thread_nr<threads.size(); thread_nr++)
    {
      out << "ASSIGN init(t" << thread_nr << ".started):=";

      if(thread_nr==0)
        out << "1";
      else
        out << "0";
      
      out << ";" << std::endl;

      out << "ASSIGN next(t" << thread_nr << ".started):=";
      
      if(thread_nr==0)
      {
        // the 'main' thread
        out << "1";
      }
      else
      {
        // any 'children'
        // they start on START_TREAD, and end on END_THREAD
        
        out << "case" << std::endl
            << "    t" << thread_nr << ".end_thread: 0; -- thread ends" << std::endl
            << "    t" << thread_nr << ".started: 1; -- already running" << std::endl
            << "    1: ";

        bool first=true;

        for(unsigned thread_nr2=0; thread_nr2<threads.size(); thread_nr2++)
        {
          if(first) first=false; else out << "+";
          out << "t" << thread_nr2 << ".start_thread_" << thread_nr;
        }

        out << ">=1;" << std::endl;
        
        out << "  esac";
      }
      
      out << ";" << std::endl;
    }

    out << std::endl;

    out << "-- exactly one thread runs at a time" << std::endl;

    out << "INVAR ";

    for(unsigned thread_nr=0; thread_nr<threads.size(); thread_nr++)
    {
      if(thread_nr!=0) out << "+";
      out << "t" << thread_nr << ".runs";
    }
    
    out << "=1";

    out << std::endl;
    out << std::endl;

    // the thread module

    out << "--" << std::endl;
    out << "-- Thread Module" << std::endl;
    out << "--" << std::endl;
    out << std::endl;
    out << "MODULE thread" << "(initial_PC";

    // the predicates

    for(unsigned i=0;
        i<abstract_model.variables.size();
        i++)
      out << ", " << variable_names[i];

    out << ")" << std::endl;
    out << std::endl;

    build_smv_file(abstract_model, out);
  }
}

/*******************************************************************\

Function: modelchecker_smvt::build_smv_file

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void modelchecker_smvt::build_smv_file(
  const abstract_modelt &abstract_model,  
  std::ostream &out)
{
  build_smv_file_local_variables(abstract_model, out);
  build_smv_file_guards(abstract_model, out);
  build_smv_file_control(abstract_model, out);
  build_smv_file_model(abstract_model, out);
  build_smv_file_sync(abstract_model, out);
  build_smv_file_spec(abstract_model, out);
}

/*******************************************************************\

Function: modelchecker_smvt::build_smv_file_local_variables

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void modelchecker_smvt::build_smv_file_local_variables(
  const abstract_modelt &abstract_model,
  std::ostream &out)
{
  //
  // runs-bit
  //

  if(threaded)
    out << "VAR runs: boolean;" << std::endl
        << "VAR started: boolean;" << std::endl
        << "INVAR !started -> !runs" << std::endl
        << std::endl;
  else
    out << "DEFINE runs:=1;" << std::endl
        << std::endl;

  //
  // Program counter
  //

  unsigned number_of_instructions=inlined.PC_map.size();

  out << "-- program counter\n"
         "-- " << number_of_instructions << " is the \"terminating\" PC\n"
         "\n"
         "VAR PC: 0.."
      << number_of_instructions
      << ";\n"
         "\n";

  out << "-- initial PC\n"
         "\n"
         "ASSIGN init(PC):=" << (threaded?"initial_PC":"0") << ";\n"
         "\n";
}

/*******************************************************************\

Function: modelchecker_smvt::build_smv_file_global_variables

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void modelchecker_smvt::build_smv_file_global_variables
 (const abstract_modelt &abstract_model,
  std::ostream &out)
{
  //
  // Program variables
  //

  out << "-- variables of the abstract program\n"
         "\n";

  size_t max_len=0;

  for(unsigned i=0;
      i<abstract_model.variables.size();
      i++)
    max_len=std::max(max_len, variable_names[i].size());

  for(unsigned i=0;
      i<abstract_model.variables.size();
      i++)
  {
    out << "VAR " << variable_names[i]
        << ": boolean;";

    if(abstract_model.variables[i].description!="")
    {
      for(unsigned j=0; j<(max_len+1-variable_names[i].size()); j++)
        out << " ";

      out << "-- " << abstract_model.variables[i].description;
    }

    out << std::endl;
  }

  out << std::endl;
}

/*******************************************************************\

Function: modelchecker_smvt::build_smv_file_guards

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void modelchecker_smvt::build_smv_file_guards(
  const abstract_modelt &abstract_model,
  std::ostream &out)
{
  //
  // nondet choice variables
  //

  out << "-- non-deterministic choice\n"
         "\n";

  for(nondet_symbolst::const_iterator
      it=nondet_symbols.begin();
      it!=nondet_symbols.end();
      it++)
    out << "VAR " << it->second << ": boolean;\n";

  out << "\n";

  //
  // Generate DEFINEs for guards
  //

  out << "-- guards\n"
         "\n";

  for(unsigned PC=0; PC<inlined.PC_map.size(); PC++)
  {
    abstract_programt::instructiont &instruction=
      *inlined.PC_map[PC].original;
  
    if(instruction.is_goto() || instruction.is_assume() ||
       instruction.is_assert())
    {
      if(!instruction.location.is_nil())
        out << "-- " << instruction.location << std::endl;

      out << "DEFINE guard" << PC << ":=";
      
      if(instruction.code.transition_relation.constraints.empty())
        out << instantiate(instruction.guard) << ";" << std::endl;
      else
      {
        if(instruction.is_goto())
        {
          const exprt &schoose=
            instruction.code.transition_relation.constraints.front();
          exprt target=
            convert_schoose_expression(schoose, instruction.guard);
          out << instantiate(target) << ";" << std::endl;
        }
        else
        {
          assert(instruction.is_assume());

          out << "(" << instantiate(instruction.guard) << ")";

          for(abstract_transition_relationt::constraintst::const_iterator
            e_it=instruction.code.transition_relation.constraints.begin();
            e_it!=instruction.code.transition_relation.constraints.end();
            e_it++)
          {
            out << " & (" << instantiate(*e_it) << ')';
          }

          out << ";" << std::endl;
        }
      }
    }
  }

  out << std::endl;
}

/*******************************************************************\

Function: modelchecker_smvt::build_threads

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void modelchecker_smvt::build_threads(threadst &dest)
{
  dest.push_back(threadt());
  dest.back().initial_PC=0;

  for(unsigned PC=0; PC<inlined.PC_map.size(); PC++)
  {
    const abstract_programt::instructiont &instruction=
      *inlined.PC_map[PC].original;

    if(instruction.is_start_thread())
    {
      dest.push_back(threadt());
      dest.back().initial_PC=PC;
    }
  }
}

/*******************************************************************\

Function: modelchecker_smvt::build_targets

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void modelchecker_smvt::build_targets(unsigned PC, std::ostream &out)
{
  const inlinedt::instructiont &instruction=inlined.PC_map[PC];

  if(instruction.targets.size()==1)
  {
    out << instruction.targets.front();
  }
  else
  {
    if(instruction.targets.empty())
      throw "no targets for branch";
  
    if(instruction.targets.size()==1)
      out << instruction.targets.front();
    else
    {
      out << "{ ";

      for(inlinedt::instructiont::targetst::const_iterator
          t_it=instruction.targets.begin();
          t_it!=instruction.targets.end();
          t_it++)
      {
        if(t_it!=instruction.targets.begin())
          out << ", ";
        
        out << *t_it;
      }
      
      out << " }";
    }
  }
}

/*******************************************************************\

Function: modelchecker_smvt::build_smv_file_control

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void modelchecker_smvt::build_smv_file_control(
  const abstract_modelt &abstract_model,
  std::ostream &out)
{
  unsigned number_of_instructions=inlined.PC_map.size();

  //
  // Generate control flow
  //

  out << "-- control flow\n"
         "\n"
         "ASSIGN next(PC):=case\n"
         "    !runs: PC;" << std::endl;

  for(unsigned PC=0; PC<inlined.PC_map.size(); PC++)
  {
    const abstract_programt::instructiont &instruction=
      *inlined.PC_map[PC].original;
  
    if(!instruction.location.is_nil())
      out << "    -- " << instruction.location << std::endl;

    out << "    PC=" << PC << ": ";

    if(instruction.is_goto())
    {
      if(instruction.guard.is_true())
      {
        build_targets(PC, out);
        out << "; -- goto (without guard)";
      }
      else
      {
        out << "case  -- goto (with guard)\n";
        out << "      guard" << PC
            << ": ";
        build_targets(PC, out);
        out << ";\n";
        out << "      1: " << PC+1 << ";" << std::endl;
        out << "    esac;";
      }
    }
    else if(instruction.is_assume() || instruction.is_assert())
    {
      if(instruction.guard.is_true())
        out << PC+1 << "; -- assume/assert with true guard";
      else
      {
        out << "case  -- assume/assert\n";
        out << "      guard" << PC
            << ": " << PC+1 << ";\n";
        out << "      1: " << PC << ";" << std::endl;
        out << "    esac;";
      }
    }
    else if(instruction.is_atomic_begin())
      out << PC+1 << "; -- atomic_begin";
    else if(instruction.is_atomic_end())
      out << PC+1 << "; -- atomic_end";
    else if(instruction.is_other())
      out << PC+1 << "; -- other";
    else if(instruction.is_decl())
      out << PC+1 << "; -- decl";
    else if(instruction.is_assign())
      out << PC+1 << "; -- assign";
    else if(instruction.is_function_call())
      out << PC+1 << "; -- function call";
    else if(instruction.is_skip())
      out << PC+1 << "; -- skip";
    else if(instruction.is_end_function())
      out << PC+1 << "; -- end_function";
    else if(instruction.is_location())
      out << PC+1 << "; -- location";
    else if(instruction.is_start_thread())
    {
      out << "case initial_PC=" << PC << ": " << PC+1 << "; 1: ";
      build_targets(PC, out);
      out << "; esac; -- start_thread";
    }
    else if(instruction.is_end_thread())
    {
      if(threaded)
        out << "initial_PC; -- end_thread";
      else
        out << PC << "; -- end_thread";
    }
    else if(instruction.is_return())
    {
      build_targets(PC, out);
      out << "; -- return";
    }
    else
      throw "unknown statement";

    out << std::endl;
  }

  out << "    -- infinite loop for termination\n"
         "    PC=" << number_of_instructions
      << ": " << number_of_instructions 
      << ";\n";
 
  out << "  esac;\n"
         "\n";
}

/*******************************************************************\

Function: modelchecker_smvt::build_smv_file_model

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void modelchecker_smvt::build_smv_file_model(
  const abstract_modelt &abstract_model,
  std::ostream &out)
{
  //
  // Generate TRANS for the abstract transitions
  //

  out << "-- the transition constraints\n"
         "\n";

  for(unsigned PC=0; PC<inlined.PC_map.size(); PC++)
  {
    const abstract_programt::instructiont &instruction=
      *inlined.PC_map[PC].original;
  
    if(!instruction.location.is_nil())
      out << "-- " << instruction.location << std::endl;

    out << "    -- FROM Predicates:";
    for(std::set<unsigned>::const_iterator
        p_it=instruction.code.transition_relation.from_predicates.begin();
        p_it!=instruction.code.transition_relation.from_predicates.end();
        p_it++)
      out << " " << variable_names[*p_it];

    out << std::endl;

    switch(instruction.type)
    {
    case GOTO:
    case FUNCTION_CALL:
    case RETURN:
    case DEAD:
    case ASSUME:
    case ASSERT:
    case START_THREAD:
    case END_THREAD:
    case END_FUNCTION:
    case LOCATION:
    case SKIP:
    case ATOMIC_BEGIN:
    case ATOMIC_END:
      if(!abstract_model.variables.empty())
      {
        out << "TRANS (PC=" << PC << " & runs) -> ";

        for(unsigned i=0;
            i<abstract_model.variables.size();
            i++)
        {
          if((i%2)==1)
            out << std::endl << "             ";

          if(i!=0) out << " & ";
          out << "next(" << variable_names[i]
              << ")=" << variable_names[i];
        }

        out << std::endl;
      }      
      break;

    case ASSIGN:      
    case OTHER:
    case DECL:
      {
        out << "TRANS (PC=" << PC << " & runs) -> ";

        unsigned cnt=0;

        for(unsigned i=0; i<abstract_model.variables.size(); i++)
        {
          abstract_transition_relationt::valuest::const_iterator
            v_it=instruction.code.transition_relation.values.find(i);

          const exprt &value=
            v_it==instruction.code.transition_relation.values.end()?
              exprt("unchanged"):v_it->second;

          if(value.is_not_nil())
          {
            if((cnt%2)==1)
              out << std::endl << "             ";

            if(cnt!=0) out << " & ";
            out << "next(" << variable_names[i]
                << ")=";

            if(value.id()=="unchanged")
              out << variable_names[i];
            else
              out << instantiate(value);

            cnt++;
          }
        }
        
        if(cnt==0) out << "1";

        out << std::endl;
      }

      if(!instruction.code.transition_relation.constraints.empty())
      {
        out << "TRANS (PC=" << PC << " & runs) -> ";

        for(abstract_transition_relationt::constraintst::const_iterator
            e_it=instruction.code.transition_relation.constraints.begin();
            e_it!=instruction.code.transition_relation.constraints.end();
            e_it++)
        {
          if(e_it!=instruction.code.transition_relation.constraints.begin())
            out << "              & ";

          out << '(' << instantiate(*e_it) << ')' << std::endl;
        }
      }
      break;
      
    default:
      assert(false);
    }

    out << "    -- TO Predicates:";
    for(std::set<unsigned>::const_iterator
        p_it=instruction.code.transition_relation.to_predicates.begin();
        p_it!=instruction.code.transition_relation.to_predicates.end();
        p_it++)
      out << " " << variable_names[*p_it];

    out << std::endl;
  }

  // termination state

  if(!abstract_model.variables.empty())
  {
    out << "-- termination" << std::endl;
    out << "TRANS (PC=" << inlined.PC_map.size() << " & runs) -> ";

    for(unsigned i=0;
        i<abstract_model.variables.size();
        i++)
    {
      if((i%2)==1)
        out << std::endl << "             ";

      if(i!=0) out << " & ";
      out << "next(" << variable_names[i]
          << ")=" << variable_names[i];
    }

    out << std::endl;
  }

  out << std::endl;
}

/*******************************************************************\

Function: modelchecker_smvt::build_smv_file_spec

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void modelchecker_smvt::build_smv_file_spec(
  const abstract_modelt &abstract_model,
  std::ostream &out)
{
  //
  // Generate SPEC from assertions
  //

  out << "-- the specification\n"
         "\n";

  for(unsigned PC=0; PC<inlined.PC_map.size(); PC++)
  {
    const abstract_programt::instructiont &instruction=
      *inlined.PC_map[PC].original;

    if(instruction.is_assert())
    {
      if(!instruction.location.is_nil())
        out << "-- " << instruction.location << std::endl;

      out << "SPEC AG ((PC=" << PC
          << " & runs) -> guard" << PC << ")" << std::endl;
    }
  }

  out << std::endl;
}

/*******************************************************************\

Function: modelchecker_smvt::build_smv_file_sync

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void modelchecker_smvt::build_smv_file_sync(
  const abstract_modelt &abstract_model,
  std::ostream &out)
{
  //
  // Generate start_thread_...
  //
  
  if(!threaded) return;

  out << "-- thread startup and termination\n"
         "\n";
         
  unsigned start_thread_nr=0;
  bool found;

  for(unsigned PC=0; PC<inlined.PC_map.size(); PC++)
  {
    const abstract_programt::instructiont &instruction=
      *inlined.PC_map[PC].original;
    
    if(instruction.is_start_thread())
    {
      start_thread_nr++;
      out << "DEFINE start_thread_" << start_thread_nr << ":=(PC=" << PC << " & runs);";
      out << std::endl;
    }
  }
  
  //
  // Generate end_thread
  //
  
  out << "DEFINE end_thread:=";
  found=false;

  for(unsigned PC=0; PC<inlined.PC_map.size(); PC++)
  {
    const abstract_programt::instructiont &instruction=
      *inlined.PC_map[PC].original;
    
    if(instruction.is_end_thread())
    {
      if(found) out << " | "; else found=true;
      out << "(PC=" << PC << " & runs)";
    }
  }
  
  if(!found) out << "0";

  out << ";" << std::endl;
  out << std::endl;
}

/*******************************************************************\

Function: modelchecker_smvt::instantiate

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string modelchecker_smvt::instantiate(const exprt &expr)
{
  exprt tmp(expr);
  instantiate_expression(tmp);
  std::string tmp_string;
  expr2smv(tmp, tmp_string);
  return tmp_string;
}

/*******************************************************************\

Function: modelchecker_smvt::instantiate_expression

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void modelchecker_smvt::instantiate_expression(exprt &expr)
{
  Forall_operands(it, expr)
    instantiate_expression(*it);

  if(expr.id()==ID_predicate_symbol)
  {
    unsigned p=atoi(expr.get(ID_identifier).c_str());
    expr.id(ID_symbol);
    expr.set(ID_identifier, variable_names[p]);
  }
  else if(expr.id()==ID_predicate_next_symbol)
  {
    unsigned p=atoi(expr.get(ID_identifier).c_str());
    expr.id(ID_next_symbol);
    expr.set(ID_identifier, variable_names[p]);
  }
  else if(expr.id()==ID_nondet_symbol)
  {
    nondet_symbolst::const_iterator it=
      nondet_symbols.find(
        static_cast<const exprt &>(expr.find("expression")));

    if(it==nondet_symbols.end())
      throw "failed to find nondet_symbol";

    typet type=expr.type();
    expr=exprt(ID_symbol, type);
    expr.set(ID_identifier, it->second);
  }
}

/*******************************************************************\

Function: modelchecker_smvt::convert_schoose_expression

  Inputs:

 Outputs:

 Purpose: given schoose[A,B] and a guard, 
          construct (* && !B) || (A && guard)

\*******************************************************************/

exprt modelchecker_smvt::convert_schoose_expression(
  const exprt &expr, const exprt &guard)
{
  nondet_symbolst::const_iterator it=
    nondet_symbols.find(static_cast<const exprt &>(expr.find("expression")));
  
  if(it==nondet_symbols.end())
    throw "failed to find nondet_symbol";
  
  exprt nondet("symbol", typet("bool"));
  nondet.set("identifier", it->second);
  
  exprt conj("and", typet("bool"));
  conj.move_to_operands(nondet);
  conj.copy_to_operands(expr.op1());
  conj.op1().make_not();

  //exprt disj("or", typet("bool"));
  //disj.copy_to_operands(expr.op0(), guard);

  exprt target("or", typet("bool"));

  target.move_to_operands(conj);
  target.copy_to_operands(expr.op0());
  
  return target;
}

/*******************************************************************\

Function: modelchecker_smvt::check

  Inputs:

 Outputs:

 Purpose: model check an abstract program using SMV, return
          counterexample if failed
          Return value of TRUE means the program is correct,
          if FALSE is returned, ce will contain the counterexample

\*******************************************************************/

bool modelchecker_smvt::check(
  abstract_modelt &abstract_model,
  abstract_counterexamplet &counterexample)
{
  std::string temp_base="cegar_tmp";

  std::string temp_smv=temp_base+"_abstract.smv";
  std::string temp_smv_out1=temp_base+"_smv_out1";
  std::string temp_smv_out2=temp_base+"_smv_out2";
  std::string temp_smv_out_ce=temp_base+"_abstract.out";
  
  remove(temp_smv_out1.c_str());
  remove(temp_smv_out2.c_str());
  remove(temp_smv_out_ce.c_str());

  get_variable_names(abstract_model);
  get_nondet_symbols(abstract_model);
  
  inlined.build(abstract_model);

  threadst threads;
  build_threads(threads);

  {
    std::ofstream out(temp_smv.c_str());
    build_smv_file(abstract_model, threads, out);
  }

  if(!inlined.has_assertion())
  {
    status("Property holds trivially");
    return true;
  }

  {
    std::string command;

    switch(engine)
    {
    case NUSMV:
      command="NuSMV -f -dynamic";
      status(std::string("Running NuSMV: ")+command);
      break;
      
    case CMU_SMV:
      status(std::string("Running CMU SMV: ")+command);
      command="smv";
      break;

    case CADENCE_SMV:
      command="smv -force -sift";
      status(std::string("Running Cadence SMV: ")+command);
      break;

    case SATMC:
      command="satmc";
      status(std::string("Running SATMC")+command);
      break;
      
    default:
      assert(false);
    }

    command+=" "+temp_smv+" >"+temp_smv_out1+
             " 2>"+temp_smv_out2;

    system(command.c_str());
  }

  bool result;

  {
    std::ifstream out1(temp_smv_out1.c_str()),
                  out2(temp_smv_out2.c_str()),
                  out_ce(temp_smv_out_ce.c_str());

    result=read_result(
      out1,
      out2,
      out_ce,
      abstract_model, threads,
      counterexample);
  }

  return result;
}

/*******************************************************************\

Function: modelchecker_smvt::save

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void modelchecker_smvt::save(
  abstract_modelt &abstract_model,
  unsigned sequence)
{
  std::string out_file_name="satabs."+i2string(sequence)+".smv";

  get_variable_names(abstract_model);
  get_nondet_symbols(abstract_model);
  
  inlined.build(abstract_model);

  threadst threads;
  build_threads(threads);

  std::ofstream out(out_file_name.c_str());
  build_smv_file(abstract_model, threads, out);
}
