/*******************************************************************\

Module: Interface to Model Checkers that use Boolean Programs

Author: Daniel Kroening

  Date: October 2004

\*******************************************************************/

#include <assert.h>
#include <stdlib.h>
#include <ctype.h>

#include <fstream>
#include <list>
#include <algorithm>

#include <str_getline.h>
#include <i2string.h>
#include <substitute.h>
#include <std_expr.h>

#include <bplang/expr2bp.h>

#include "modelchecker_boolean_program.h"

/*******************************************************************\

Function: modelchecker_boolean_programt::read_result_boppo_boom

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool modelchecker_boolean_programt::read_result_boppo_boom(
  std::istream &out1,
  std::istream &out2,
  abstract_modelt &abstract_model,
  abstract_counterexamplet &counterexample)
{
  std::list<std::string> file;

  while(true)
  {
    std::string line;
    if(!str_getline(out1, line)) break;
    file.push_back(line);
  }
  
  // first get result
  
  for(std::list<std::string>::const_iterator 
      it=file.begin(); it!=file.end(); it++)
    if(*it=="VERIFICATION SUCCESSFUL")
      return true;
    else if(*it=="VERIFICATION FAILED")
    {
      read_counterexample_boppo_boom(file, abstract_model, counterexample);
      return false;
    }

  throw std::string("unexpected result from ")+
        (engine==BOOM?"Boom":"Boppo");
  return false;
}

/*******************************************************************\

Function: modelchecker_boolean_programt::read_counterexample_boppo_boom

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void modelchecker_boolean_programt::read_counterexample_boppo_boom(
  const std::string &line,
  std::list<std::pair<std::string, std::string> > &assignments,
  std::list<std::string> &labels)
{
  for(std::string::size_type p=0; p<line.size();)
  {
    // skip spaces
    while(p<line.size() && line[p]==' ') p++;
    
    if(p>=line.size()) break;

    std::string::size_type p2=p;
    
    // get to next space or '='
    while(p2<line.size() && line[p2]!=' ' && line[p2]!='=')
      p2++;

    if(p2>=line.size() || line[p2]==' ')
    {
      // it's a label
      labels.push_back(std::string(line, p, p2-p));
      p=p2;
    }
    else
    {
      // it's an assignment
      std::string variable(line, p, p2-p);
      
      p=p2+1;

      // get to next space
      while(p2<line.size() && line[p2]!=' ') p2++;
      
      std::string value(line, p, p2-p);
      p=p2;
      
      assignments.push_back(std::pair<std::string, std::string>(
        variable, value));
    }
  }
}

/*******************************************************************\

Function: modelchecker_boolean_programt::read_counterexample_boppo_boom

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void modelchecker_boolean_programt::read_counterexample_boppo_boom(
  const std::list<std::string> &file,
  abstract_modelt &abstract_model,
  abstract_counterexamplet &counterexample)
{
  for(std::list<std::string>::const_iterator
      it=file.begin();
      it!=file.end();
      it++)
  {
    const std::string &line=*it;
  
    if(std::string(line, 0, 6)=="TRACE ")
    {
      abstract_statet abstract_state;
      
      // initialization
      abstract_state.predicate_values.resize(
        abstract_model.variables.size(), false);

      // for gotos
      abstract_state.branch_taken=true;
      
      std::list<std::pair<std::string, std::string> > assignments;
      std::list<std::string> labels;

      // parse      
      read_counterexample_boppo_boom(
        std::string(line, 6, std::string::npos), assignments, labels);
      
      for(std::list<std::pair<std::string, std::string> >::const_iterator
          a_it=assignments.begin();
          a_it!=assignments.end();
          a_it++)
      {
        std::string variable=a_it->first;
        const std::string &value=a_it->second;
        
        // strip function name from variable name
        {
          std::string::size_type pos=variable.find("::");
          if(pos!=std::string::npos)
            variable=std::string(variable, pos+2, std::string::npos);
        }

        if(variable.empty())
          throw "failed to get variable name";
        else if(variable[0]=='b') // checked for emptyness above
        {
          unsigned nr=atoi(variable.c_str()+1);
          if(nr>=abstract_state.predicate_values.size())
            throw "invalid variable in abstract counterexample: "+
              variable;

          abstract_state.predicate_values[nr]=atoi(value.c_str());
        }
        else if(std::string(variable, 0, 3)=="t")
        {
          abstract_state.thread_nr=atoi(value.c_str());
        }
        else if(variable=="TAKEN")
          abstract_state.branch_taken=atoi(value.c_str());
        else
          throw "unknown variable in abstract counterexample: `"+
                variable+"'";
      }

      for(std::list<std::string>::const_iterator
          l_it=labels.begin();
          l_it!=labels.end();
          l_it++)
      {
        if(std::string(*l_it, 0, 2)=="PC")
        {
          unsigned PC=atoi(l_it->c_str()+2);
          assert(PC<PC_map.size());
          abstract_state.pc=PC_map[PC];
          abstract_state.label_nr=PC;
          abstract_state.has_pc=true;
        }
      }
      
      if(abstract_state.has_pc)
        counterexample.steps.push_back(abstract_state);
    }
    else if(line=="LOOP [")
    {
      counterexample.steps.push_back(abstract_stept(abstract_stept::LOOP_BEGIN));
    }
    else if(line=="LOOP ]")
    {
      counterexample.steps.push_back(abstract_stept(abstract_stept::LOOP_END));
    }
  }

  assert(!counterexample.steps.empty());
}

/*******************************************************************\

Function: modelchecker_boolean_programt::build_boolean_program_file

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void modelchecker_boolean_programt::build_boolean_program_file(
  abstract_modelt &abstract_model,
  std::ostream &out)
{
  // start printing Boolean program

  out << "// automatically generated by CPROVER/SATABS\n"
         "\n";

  build_boolean_program_file_global_variables(abstract_model, out);
  build_boolean_program_file_functions(abstract_model, out);
}

/*******************************************************************\

Function: modelchecker_boolean_programt::build_boolean_program_file_local_variables

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void modelchecker_boolean_programt::build_boolean_program_file_local_variables(
  const abstract_modelt &abstract_model,
  std::ostream &out)
{
  #if 0
  //
  // Events
  //

  if(!events.empty())
  {
    out << "-- events\n"
           "\n";

    for(eventst::const_iterator it=events_waited_for.begin();
        it!=events_waited_for.end();
        it++)
    {
      out << "VAR " << "sticky_" << *it
          << ": boolean;" << std::endl;
      out << "ASSIGN init(sticky_" << *it << "):=0;"
          << std::endl;
    }

    out << std::endl;
  }
  #endif
}

/*******************************************************************\

Function: modelchecker_boolean_programt::build_boolean_program_file_global_variables

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void modelchecker_boolean_programt::build_boolean_program_file_global_variables(
  const abstract_modelt &abstract_model,
  std::ostream &out)
{
  //
  // Global program variables
  //

  out << "// variables with procedure-global scope\n"
         "\n";

  size_t max_len=0;

  for(unsigned i=0;
      i<abstract_model.variables.size();
      i++)
    if(abstract_model.variables[i].is_shared_global() ||
       abstract_model.variables[i].is_thread_local())
      max_len=std::max(max_len, variable_names[i].size());

  for(unsigned i=0;
      i<abstract_model.variables.size();
      i++)
    if(abstract_model.variables[i].is_shared_global() ||
       abstract_model.variables[i].is_thread_local())
    {
      out << "decl ";

      if(abstract_model.variables[i].is_thread_local())
        out << "thread_local ";

      out << variable_names[i] << "; ";

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
  if(!events.empty())
  {
    out << "-- events\n"
           "\n";

    for(eventst::const_iterator it=events.begin();
        it!=events.end();
        it++)
      out << "VAR " << "event_" << *it
          << ": boolean;" << std::endl;

    out << std::endl;
  }
  #endif
}

/*******************************************************************\

Function: modelchecker_boolean_programt::build_boolean_program_file_functions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void modelchecker_boolean_programt::build_boolean_program_file_functions(
  abstract_modelt &abstract_model,
  std::ostream &out)
{
  PC_map.clear();

  for(abstract_functionst::function_mapt::iterator
      f_it=abstract_model.goto_functions.function_map.begin();
      f_it!=abstract_model.goto_functions.function_map.end();
      f_it++)
    build_boolean_program_file_function(abstract_model, f_it, out);
}

/*******************************************************************\

Function: modelchecker_boolean_programt::build_boolean_program_file_function

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void modelchecker_boolean_programt::build_boolean_program_file_function(
  abstract_modelt &abstract_model,
  abstract_functionst::function_mapt::iterator f_it,
  std::ostream &out)
{
  // header
  out << "// " << f_it->first << std::endl;
  out << "void " << convert_function_name(f_it->first)
      << "() begin\n"
         "\n";

  // local variables

  {
    size_t max_len=0;
    bool has_procedure_local_variables=false;

    for(unsigned i=0;
        i<abstract_model.variables.size();
        i++)
      if(abstract_model.variables[i].is_procedure_local())
      {
        max_len=std::max(max_len, variable_names[i].size());
        has_procedure_local_variables=true;
      }

    if(has_procedure_local_variables)
    {
      out << "      // the procedure-local variables\n"
             "\n";
        
      for(unsigned i=0;
          i<abstract_model.variables.size();
          i++)
        if(abstract_model.variables[i].is_procedure_local())
        {
          out << "  decl " << variable_names[i] << "; ";

          if(abstract_model.variables[i].description!="")
          {
            for(unsigned j=0; j<(max_len+1-variable_names[i].size()); j++)
              out << " ";

            out << "// " << abstract_model.variables[i].description;
          }

          out << std::endl;
        }

      out << std::endl;
    }
  }

  // initialize globals if this is main
  // just to make sure that there is no misunderstanding
  // about the initial value of any global variable

  if(f_it->first=="main")
  {
    out << "      // initialization of the shared-global and thread-local variables\n"
           "\n";

    for(unsigned i=0;
        i<abstract_model.variables.size();
        i++)
      if(abstract_model.variables[i].is_shared_global() ||
         abstract_model.variables[i].is_thread_local())
      {
        out << "      " << variable_names[i] << ":=*; ";
        out << std::endl;
      }

    out << std::endl;
  }

  abstract_programt &abstract_program=f_it->second.body;
  
  // control flow
  
  locationt previous_location;

  for(abstract_programt::instructionst::iterator
      it=abstract_program.instructions.begin();
      it!=abstract_program.instructions.end();
      it++)
  {
    unsigned PC=PC_map.size();
    PC_map.push_back(it);

    if(!it->location.is_nil() &&
       it->location!=previous_location)
    {
      out << "    // " << it->location << std::endl;
      previous_location=it->location;
    }
      
    if(!it->code.transition_relation.from_predicates.empty())
    {
      out << "    // FROM Predicates:";
      for(std::set<unsigned>::const_iterator
          p_it=it->code.transition_relation.from_predicates.begin();
          p_it!=it->code.transition_relation.from_predicates.end();
          p_it++)
        out << " " << variable_names[*p_it];

      out << std::endl;
    }

    if(it->is_target())
    {
      std::string label="l"+i2string(it->target_number);
      out << std::setw(4) << label << ":" << std::endl;
    }

    {
      std::string label="PC"+i2string(PC);
      out << std::setw(4) << label << ": ";
    }

    if(it->is_goto())
    {
      if(!it->guard.is_true())
      {
        out << "if ";
        exprt tmp(it->guard);
        instantiate_expression(tmp);
        if(!it->code.transition_relation.constraints.size())
          out << expr2bp(tmp);
        else
        {
          exprt &choose=
            it->code.transition_relation.constraints.front();
          exprt tmp0(choose.op0()); instantiate_expression(tmp0);
          exprt tmp1(choose.op1()); instantiate_expression(tmp1);

          out << "(schoose[" << expr2bp(tmp0); // << " & " << expr2bp(tmp);
          out << "," << expr2bp(tmp1) <<  "])";
        }
        out << " then ";
      }
      
      out << "goto ";
      
      for(abstract_programt::instructiont::targetst::const_iterator
          gt_it=it->targets.begin();
          gt_it!=it->targets.end();
          gt_it++)
      {
        if(gt_it!=it->targets.begin()) out << ", ";
        out << "l" << (*gt_it)->target_number;
      }
      
      out << ";";

      if(!it->guard.is_true())
        out << " fi;";
    }
    else if(it->is_start_thread())
    {
      out << "start_thread goto ";

      for(abstract_programt::instructiont::targetst::const_iterator
          gt_it=it->targets.begin();
          gt_it!=it->targets.end();
          gt_it++)
      {
        if(gt_it!=it->targets.begin()) out << ", ";
        out << "l" << (*gt_it)->target_number;
      }
      
      out << ";";
    }
    else if(it->is_end_thread())
    {
      out << "end_thread;";
    }
    else if(it->is_assume())
    {
      exprt tmp(it->guard);
      instantiate_expression(tmp);
      out << "assume(" << expr2bp(tmp);

      const std::list<exprt> &constraints=
        it->code.transition_relation.constraints;
      if(!constraints.empty())
      {
        for(std::list<exprt>::const_iterator
            it=constraints.begin();
            it!=constraints.end();
            it++)
        {
          exprt tmp(*it);
          instantiate_expression(tmp);
          out << " & " << '(' << expr2bp(tmp) << ')';
        }
      }
      out << ");";
    }
    else if(it->is_assert())
    {
      std::string code;
      exprt tmp(it->guard);
      instantiate_expression(tmp);
      out << "assert(" << expr2bp(tmp) << ");";
    }
    else if(it->is_dead())
    {
      out << "dead;";
    }
    else if(it->is_atomic_begin())
    {
      out << "atomic_begin;";
    }
    else if(it->is_atomic_end())
    {
      out << "atomic_end;";
    }
    else if(it->is_other() ||
            it->is_assign() ||
            it->is_decl())
    {
      bool first=true;

      for(unsigned i=0; i<abstract_model.variables.size(); i++)
        if(it->code.transition_relation.values.count(i)!=0)
        {
          if(first) first=false; else out << ",";
          out << variable_names[i];
        }
        
      if(first) // none changed?
      {
        out << "skip; // no predicates changed";
      }
      else
      {
        out << " := ";

        first=true;

        for(unsigned i=0; i<abstract_model.variables.size(); i++)
        {
          abstract_transition_relationt::valuest::const_iterator
            v_it=it->code.transition_relation.values.find(i);
          
          if(v_it!=it->code.transition_relation.values.end())
          {
            const exprt &value=v_it->second;

            if(first) first=false; else out << ",";

            if(value.is_nil())
              out << "*";
            else
            {
              exprt tmp(value);
              instantiate_expression(tmp);
              out << expr2bp(tmp);
            }
          }
        }
        
        // constraints
        
        const std::list<exprt> &constraints=
          it->code.transition_relation.constraints;
        
        if(!constraints.empty())
        {
          out << " constrain";
          
          for(std::list<exprt>::const_iterator
              it=constraints.begin();
              it!=constraints.end();
              it++)
          {
            exprt tmp(*it);
            instantiate_expression(tmp);
            
            if(it!=constraints.begin()) out << " &";
            out << std::endl << "    "
                << '(' << expr2bp(tmp) << ')';
          }
        }
          
        out << ";";
      }
    }
    else if(it->is_skip() || it->is_end_function())
    {
      out << "skip;";
    }
    else if(it->is_function_call())
    {
      const code_function_callt &call=
        to_code_function_call(it->code.concrete_pc->code);
      if(call.function().id()!="symbol")
        throw "expected symbol as function argument";
      const symbol_exprt &symbol=to_symbol_expr(call.function());
      const irep_idt &id=symbol.get_identifier();

      out << convert_function_name(id)
          << "();";
    }
    else if(it->is_return())
    {
      out << "return;";
    }
    else if(it->is_location())
    {
      out << "skip; // location only";
    }
    else
      throw "unknown statement";

    out << std::endl;

    if(!it->code.transition_relation.to_predicates.empty())
    {
      out << "    // TO Predicates:";
      for(std::set<unsigned>::const_iterator
          p_it=it->code.transition_relation.to_predicates.begin();
          p_it!=it->code.transition_relation.to_predicates.end();
          p_it++)
        out << " " << variable_names[*p_it];

      out << std::endl;
    }

    out << std::endl;
  }
  
  out << "end\n\n";
}

/*******************************************************************\

Function: modelchecker_boolean_programt::instantiate_expression

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void modelchecker_boolean_programt::instantiate_expression(exprt &expr)
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
    expr=exprt(ID_nondet_bool);
  }
}

/*******************************************************************\

Function: modelchecker_boolean_programt::check

  Inputs:

 Outputs:

 Purpose: model check an abstract program using SMV, return
          counterexample if failed
          Return value of TRUE means the program is correct,
          if FALSE is returned, ce will contain the counterexample

\*******************************************************************/

bool modelchecker_boolean_programt::check(
  abstract_modelt &abstract_model,
  abstract_counterexamplet &counterexample)
{
  std::string temp_base="cegar_tmp";

  std::string temp_boolean_program=temp_base+"_abstract.bp";
  std::string temp_boolean_program_out1=temp_base+"_boolean_program_out1";
  std::string temp_boolean_program_out2=temp_base+"_boolean_program_out2";

  build(abstract_model, temp_boolean_program);

  {
    std::string command;

    switch(engine)
    {
    case BOPPO:
      status(std::string("Running BOPPO"));
      command="boppo --compact-trace --por";
      if(loop_detection)
        {
          command+=" --loop-detection";
        }
      break;
      
    case BOOM:
      status(std::string("Running BOOM"));
      command="boom -t";
      if(max_threads!=0)
        command+=" --threadbound "+i2string(max_threads);
      break;
      
    case BEBOP:
      status(std::string("Running BEBOP"));
      throw "Support for Bebop not yet implemented";
      break;
    
    case MOPED:
      status(std::string("Running MOPED"));
      throw "Support for Moped not yet implemented";
      break;
    
    default:
      assert(false);
    }

    command+=" "+temp_boolean_program+" >"+temp_boolean_program_out1+
             " 2>"+temp_boolean_program_out2;

    system(command.c_str());
  }

  bool result;

  {
    std::ifstream out1(temp_boolean_program_out1.c_str()),
                  out2(temp_boolean_program_out2.c_str());

    switch(engine)
    {
    case BOPPO:
    case BOOM:
      result=read_result_boppo_boom(
        out1, out2, abstract_model, counterexample);
      break;
    
    default:
      assert(false);
    }
  }
  
  return result;
}

/*******************************************************************\

Function: modelchecker_boolean_programt::convert_function_name

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

std::string modelchecker_boolean_programt::convert_function_name(
  const irep_idt &name)
{
  std::string result=name.as_string();

  for(unsigned i=0; i<result.size(); i++)
  {
    char ch=result[i];
    if(isalnum(ch) || ch=='_')
    { // ok
    }
    else if(ch==':')
      result[i]='$';
    else
      result[i]='_';
  }

  return result;
}

/*******************************************************************\

Function: modelchecker_boolean_programt::build

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void modelchecker_boolean_programt::build(
  abstract_modelt &abstract_model,
  const std::string &out_file_name)
{
  get_variable_names(abstract_model);
  //get_nondet_symbols(abstract_model);
  //get_events(abstract_model);

  std::ofstream out(out_file_name.c_str());
  build_boolean_program_file(abstract_model, out);
}

/*******************************************************************\

Function: modelchecker_boolean_programt::save

  Inputs:

 Outputs:

 Purpose: 

\*******************************************************************/

void modelchecker_boolean_programt::save(
  abstract_modelt &abstract_model,
  unsigned sequence)
{
  build(abstract_model, "satabs."+i2string(sequence)+".bp");
}
