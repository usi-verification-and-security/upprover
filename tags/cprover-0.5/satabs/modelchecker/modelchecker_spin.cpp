/*******************************************************************\

Module: SPIN Model Checker Interface

Author: Daniel Kroening

  Date: March 2004

\*******************************************************************/

#include <assert.h>
#include <stdlib.h>
#include <ctype.h>

#include <fstream>
#include <list>
#include <algorithm>

#include <str_getline.h>
#include <promela/expr2promela.h>
#include <i2string.h>

#include "modelchecker_spin.h"

/*******************************************************************\

Function: modelchecker_spint::read_result

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool modelchecker_spint::read_result
 (std::istream &out1,
  std::istream &out2,
  const abstract_modelt &abstract_model,
  abstract_counterexamplet &counterexample)
{
  #if 0
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
      throw "SPIN error";
  }

  // now read output

  {
    std::list<std::string> file;

    while(true)
    {
      std::string line;
      if(!str_getline(out1, line)) break;
      file.push_back(line);
    }

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
          status("SPIN produced counterexample");
          read_counterexample(file, it, abstract_model,
                              counterexample);
          status("SPIN counterexample sucessfully read");

          // show it
          //std::cout << counterexample;
          return false;
        }
        else
          throw "unexpected reply from SPIN: \""+*it+"\"";
      }
    }
  }
  #endif

  throw "not yet implemented";

  return true;
}

/*******************************************************************\

Function: modelchecker_spint::read_counterexample

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void modelchecker_spint::read_counterexample
 (const std::list<std::string> &file,
  std::list<std::string>::const_iterator it,
  const abstract_modelt &abstract_model,
  abstract_counterexamplet &counterexample)
{
  #if 0
  while(it!=file.end() && 
        (std::string(*it, 0, 1)=="*" ||
        (std::string(*it, 0, 1)=="-")))
    it++;

  abstract_statet abstract_state;
  abstract_state.predicate_values.resize(
    abstract_model.variables.size());

  bool data_set=false;

  std::vector<smv_ce_thread_infot> thread_infos;
  thread_infos.resize(abstract_model.threads.size());

  {
    unsigned i=0;
    forall_abstract_threads(t_it, abstract_model.threads)
      thread_infos[i++].build(*t_it);
  }

  for(; it!=file.end(); it++)
  {
    std::cout << "Xx " << *it << "\n";

    if(std::string(*it, 0, 3)=="-- ")
      break;
    else if(*it=="resources used:")
      break;
    else if(std::string(*it, 0, 6)=="state " ||
            std::string(*it, 0, 9)=="-> State " ||
            *it=="")
    {
      if(!data_set) continue;

      read_counterexample_store(
        counterexample, thread_infos, abstract_state);

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
      else if(variable[0]=='b') // checked for emptyness above
      {
        unsigned nr=atoi(variable.c_str()+1);
        if(nr>=abstract_state.predicate_values.size())
          throw "invalid variable in abstract counterexample: "+
            variable;

        abstract_state.predicate_values[nr]=atoi(value.c_str());
        data_set=true;
      }
      else if(std::string(variable, 0, 5)=="guard")
      {
        unsigned nr=atoi(variable.c_str()+5);
        if(nr>=thread_infos[thread_nr].guards.size())
          throw "invalid variable in abstract counterexample: "+
            variable;

        thread_infos[thread_nr].guards[nr]=atoi(value.c_str());
      }
      else if(std::string(variable, 0, 6)=="event_")
      {
      }
      else if(std::string(variable, 0, 7)=="sticky_")
      {
      }
      else if(std::string(variable, 0, 6)=="nondet")
      {
      }
      else
        throw "unknown variable in abstract counterexample: "+
              original_variable+" (stripped: "+variable+")";
    }
  }

  if(data_set)
    read_counterexample_store(
      counterexample, thread_infos, abstract_state);
  #endif

  throw "not yet implemented";
}

/*******************************************************************\

Function: modelchecker_spint::build_promela_file

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void modelchecker_spint::build_promela_file(
  const abstract_modelt &abstract_model,
  std::ostream &out)
{
  // start printing Promela

  out << "// automatically generated by CPROVER/CEGAR\n"
         "\n";

  build_promela_file_global_variables(abstract_model, out);

  out << "//" << std::endl;
  out << "// Main Thread" << std::endl;
  out << "//" << std::endl;
  out << std::endl;
  out << "proctype main_thread(){\n";

  build_promela_file_control(abstract_model, out);

  out << "}\n\n";

  out << "init{\n";

  out << "  run main_thread();" << std::endl;

  out << "}" << std::endl;
}

/*******************************************************************\

Function: modelchecker_spint::build_promela_file_global_variables

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void modelchecker_spint::build_promela_file_global_variables
 (const abstract_modelt &abstract_model,
  std::ostream &out)
{
  //
  // Program variables
  //

  out << "// variables of the abstract program\n"
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
    out << "bool " << variable_names[i]
        << "=false;";

    if(abstract_model.variables[i].description!="")
    {
      for(unsigned j=0; j<(max_len+1-variable_names[i].size()); j++)
        out << " ";

      out << "// " << abstract_model.variables[i].description;
    }

    out << std::endl;
  }

  out << std::endl;

  //
  // Events
  //

  #if 0
  for(unsigned thread_nr=0;
      thread_nr<events_waited_for.size();
      thread_nr++)
    if(!events_waited_for[thread_nr].empty())
    {
      out << "// Events for thread " << thread_nr << std::endl;

      out << "bool ";

      for(eventst::const_iterator it=events_waited_for[thread_nr].begin();
          it!=events_waited_for[thread_nr].end();
          it++)
      {
        if(it!=events_waited_for[thread_nr].begin())
          out << ", ";

        out << "t" << thread_nr << "_event_" << *it << "=false";
      }

      out << ";" << std::endl << std::endl;
    }
  #endif

  out << std::endl;
}

/*******************************************************************\

Function: modelchecker_spint::build_promela_file_control

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void modelchecker_spint::build_promela_file_control(
  const abstract_modelt &abstract_model,
  std::ostream &out)
{
  //
  // Generate control flow
  //

  for(unsigned PC=0; PC<inlined.PC_map.size(); PC++)
  {
    const inlinedt::instructiont &instruction=inlined.PC_map[PC];
    
    if(!instruction.original->location.is_nil())
      out << "    // " << instruction.original->location << std::endl;

    std::string guard_string;

    {
      exprt tmp(instruction.original->guard);
      instantiate_expression(tmp);
      guard_string=expr2promela(tmp, concrete_model.ns);
    }

    out << "  l" << PC << ": ";

    if(PC==0) out << "end: ";

    if(instruction.original->is_goto())
    {
      #if 0 // TODO
      targetst::const_iterator result=targets.find(it->target);
      if(result==targets.end()) throw "target not found";

      if(it->guard.is_true())
        out << "goto l" << result->second;
      else
      {
        out << "if :: (" << guard_string << ") -> goto l"
            << result->second << " :: else fi\n";
      }
      #endif
    }
    else if(instruction.original->is_assume())
    {
      throw "Spin cannot do assume";
    }
    else if(instruction.original->is_assert())
    {
      out << "assert(" << guard_string << ")";
    }
    #if 0
    else if(instruction.original->is_wait())
    {
      out << "atomic{ (";

      for(std::set<std::string>::const_iterator
          e_it=instruction.original->events.begin();
          e_it!=instruction.original->events.end();
          e_it++)
      {
        if(e_it!=instruction.original->events.begin())
          out << (instruction.original->or_semantics?" || ":" && ");

        out << "t" << thread_nr << "_event_" << *e_it;
      }

      out << ")";

      out << " ->";

      for(std::set<std::string>::const_iterator
          e_it=instruction.original->events.begin();
          e_it!=instruction.original->events.end();
          e_it++)
        out << " " << "t" << thread_nr << "_event_" << *e_it
            << "=false;";

      out << "}";
    }
    #endif
    #if 0
    else if(instruction.original->is_event())
    {
      out << "atomic{";

      for(unsigned t=0;
          t<events_waited_for.size();
          t++)
        for(std::set<std::string>::const_iterator
            e_it=instruction.original->events.begin();
            e_it!=instruction.original->events.end();
            e_it++)
          if(events_waited_for[t].find(*e_it)!=
             events_waited_for[t].end())
            out << " " << "t" << t << "_event_" << *e_it
                << "=true;";

      out << "}";
    }
    #endif
    else if(instruction.original->is_other())
    {
      build_promela_file_trans(
        abstract_model,
        instruction.original->code.transition_relation,
        out);
    }
    else
      assert(0);

    out << ";" << std::endl;
  }
}

/*******************************************************************\

Function: modelchecker_spint::build_promela_file_trans

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void modelchecker_spint::build_promela_file_trans
 (const abstract_modelt &abstract_model,
  const abstract_transition_relationt &transition_relation,
  std::ostream &out)
{
  #if 0
  std::vector<unsigned> input, output;

  for(unsigned i=0;
      i<abstract_model.variables.size();
      i++)
  {
    if(transition_relation.input_predicates.find(i)!=
       transition_relation.input_predicates.end())
      input.push_back(i);

    if(transition_relation.output_predicates.find(i)!=
       transition_relation.output_predicates.end())
      output.push_back(i);
  }

  if(output.empty())
  {
    out << "skip"; // no changes
    return;
  }

  unsigned number_of_cubes=0;

  {
    for(cubest::star_mapt::const_iterator
        s_it=transition_relation.cubes.star_map.begin();
        s_it!=transition_relation.cubes.star_map.end();
        s_it++)
      for(cubest::bitssett::const_iterator
          b_it=s_it->second.begin();
          b_it!=s_it->second.end();
          b_it++)
        number_of_cubes++;
  }

  assert(number_of_cubes!=0);

  if(number_of_cubes>=2)
    out << "if // " << number_of_cubes << " cubes" << std::endl;
 
  for(cubest::star_mapt::const_iterator
      s_it=transition_relation.cubes.star_map.begin();
      s_it!=transition_relation.cubes.star_map.end();
      s_it++)
  {
    const cubest::bitvt &stars=s_it->first;

    for(cubest::bitssett::const_iterator
        b_it=s_it->second.begin();
        b_it!=s_it->second.end();
        b_it++)
    {
      if(number_of_cubes>=2)
        out << "      :: ";

      const cubest::bitvt &bits=*b_it;

      unsigned bit=0;

      assert(stars.size()==input.size()+output.size());

      bool found_input=false;
      for(unsigned i=0; i<input.size(); i++)
        if(!stars[i])
        {
          found_input=true;
          break;
        }

      out << "atomic{ ";

      if(found_input)
      {
        out << "(";
        bool first=true;
        for(unsigned i=0; i<input.size(); i++)
        {
          if(!stars[i])
          {
            assert(bit<bits.size());

            if(first) first=false; else out << " && ";

            if(!bits[bit])
              out << "!";

            out << variable_names[input[i]];

            bit++;
          }
        }

        out << ") ->";
      }

      for(unsigned i=0; i<output.size(); i++)
      {
        if(stars[i+input.size()])
        {
          out << " if :: " << variable_names[output[i]] << "=false;"
              << " :: " << variable_names[output[i]] << "=true; fi;";
        }
        else
        {
          assert(bit<bits.size());

          out << " " << variable_names[output[i]] << "=";
          out << (bits[bit]?"true":"false");
          out << ";";
         
          bit++;
        }
      }

      out << "}";

      if(number_of_cubes>=2)
        out << std::endl;
    }
  }

  if(number_of_cubes>=2)
    out << "      fi";
  #endif
}

/*******************************************************************\

Function: modelchecker_spint::instantiate_expression

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void modelchecker_spint::instantiate_expression(exprt &expr)
{
  Forall_operands(it, expr)
    instantiate_expression(*it);

  if(expr.id()==ID_predicate_symbol)
  {
    unsigned p=atoi(expr.get(ID_identifier).c_str());
    expr.id(ID_symbol);
    expr.set(ID_identifier, variable_names[p]);
  }
  else if(expr.id()==ID_nondet_symbol)
  {
    nondet_symbolst::const_iterator it=
      nondet_symbols.find(expr.find_expr(ID_expression));

    if(it==nondet_symbols.end())
      throw "failed to find nondet_symbol";

    typet type=expr.type();
    expr=exprt(ID_symbol, type);
    expr.set(ID_identifier, it->second);
  }
}

/*******************************************************************\

Function: modelchecker_spint::check

  Inputs:

 Outputs:

 Purpose: model check an abstract program using SPIN, return
          counterexample if failed
          Return value of TRUE means the program is correct,
          if FALSE is returned, ce will contain the counterexample

\*******************************************************************/

bool modelchecker_spint::check(
  abstract_modelt &abstract_model,
  abstract_counterexamplet &counterexample)
{
  std::string temp_base="cegar_tmp";

  std::string temp_spin=temp_base+"_abstract.promela";
  std::string temp_spin_out1=temp_base+"_spin_out1";
  std::string temp_spin_out2=temp_base+"_spin_out2";

  build(abstract_model, temp_spin);

  status("Running SPIN");

  {
    std::string command;

    command="spin";

    command+=" "+temp_spin+" >"+temp_spin_out1+
             " 2>"+temp_spin_out2;

    system(command.c_str());
  }

  bool result;

  {
    std::ifstream out1(temp_spin_out1.c_str()),
                  out2(temp_spin_out2.c_str());

    result=read_result(out1, out2, abstract_model,
                       counterexample);
  }

  return result;
}

/*******************************************************************\

Function: modelchecker_spint::check

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void modelchecker_spint::build(
  abstract_modelt &abstract_model,
  const std::string &out_file_name)
{
  get_variable_names(abstract_model);
  get_nondet_symbols(abstract_model);

  inlined.build(abstract_model);

  std::ofstream out(out_file_name.c_str());
  build_promela_file(abstract_model, out);
}

/*******************************************************************\

Function: modelchecker_spint::save

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void modelchecker_spint::save(
  abstract_modelt &abstract_model,
  unsigned sequence)
{
  build(abstract_model, "satabs."+i2string(sequence)+".promela");
}
