/*******************************************************************\

Module: Model Checker Base Class

Author: Daniel Kroening
        Karen Yorav 

Date: June 2003

\*******************************************************************/

#include <i2string.h>
#include <substitute.h>

#include <std_expr.h>

#include "modelchecker.h"

/*******************************************************************\

Function: modelcheckert::is_variable_name

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool modelcheckert::is_variable_name(
  const std::string &name)
{
  if(name=="") return false;

  for(unsigned i=0; i<name.size(); i++)
    if(!isalnum(name[i]) &&
       name[i]!='_')
      return false;

  return true;
}

/*******************************************************************\

Function: modelcheckert::get_variable_names

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void modelcheckert::get_variable_names(
  const abstract_modelt &abstract_model)
{
  variable_names.resize(abstract_model.variables.size());

  for(unsigned i=0;
      i<abstract_model.variables.size();
      i++)
  {
    variable_names[i]="b"+i2string(i);

    std::string description=
      abstract_model.variables[i].description;
      
    // do some substitution
    substitute(description, " ", "_");
    substitute(description, "==", "eq");
    substitute(description, "!=", "neq");
    substitute(description, ">=", "ge");
    substitute(description, "<=", "le");
    substitute(description, ">>", "shr");
    substitute(description, "<<", "shl");
    substitute(description, "<", "lt");
    substitute(description, ">", "gt");
    substitute(description, "&", "amp");
    substitute(description, "|", "or");
    substitute(description, "+", "plus");
    substitute(description, "-", "minus");
    substitute(description, "*", "deref_");

    if(is_variable_name(description))
      variable_names[i]+="_"+description;
  }
}

/*******************************************************************\

Function: modelcheckert::enable_loop_detection

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void modelcheckert::enable_loop_detection()
{
  throw "loop detection not supported by "+description();
}

/*******************************************************************\

Function: modelcheckert::get_nondet_symbols

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void modelcheckert::get_nondet_symbols(const abstract_modelt &abstract_model)
{
  nondet_symbols.clear();

  for(abstract_functionst::function_mapt::const_iterator
      f_it=abstract_model.goto_functions.function_map.begin();
      f_it!=abstract_model.goto_functions.function_map.end();
      f_it++)
    for(abstract_programt::instructionst::const_iterator
        i_it=f_it->second.body.instructions.begin();
        i_it!=f_it->second.body.instructions.end();
        i_it++)
    {
      get_nondet_symbols(i_it->guard);
      // add nondets for refined gotos and assumes
      if ((i_it->is_goto()||i_it->is_assume())&&
          i_it->code.transition_relation.constraints.size())
          get_nondet_symbols
            (i_it->code.transition_relation.constraints.front());
    }
}

/*******************************************************************\

Function: modelcheckert::get_nondet_symbols

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void modelcheckert::get_nondet_symbols(const exprt &expr)
{
  forall_operands(it, expr)
    get_nondet_symbols(*it);

  if(expr.id()==ID_nondet_symbol ||
     expr.id()==ID_bp_schoose)
  {
    nondet_symbols.insert(std::pair<exprt, std::string>
      (static_cast<const exprt &>(expr.find(ID_expression)), 
       "nondet"+i2string(nondet_symbols.size())));
  }
}

/*******************************************************************\

Function: modelcheckert::inlinedt::build

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void modelcheckert::inlinedt::build(abstract_modelt &abstract_model)
{
  PC_map.clear();

  // start with "main"
  std::set<irep_idt> recursion_stack;
  build(abstract_model, "main", recursion_stack);
}

/*******************************************************************\

Function: modelcheckert::inlinedt::has_assertion

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool modelcheckert::inlinedt::has_assertion() const
{
  for(unsigned PC=0; PC<PC_map.size(); PC++)
    if(PC_map[PC].original->is_assert())
      return true;
      
  return false;
}

/*******************************************************************\

Function: modelcheckert::inlinedt::build

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void modelcheckert::inlinedt::build(
  abstract_modelt &abstract_model,
  const irep_idt f_id,
  std::set<irep_idt> &recursion_stack)
{
  abstract_functionst::function_mapt::iterator f_it=
    abstract_model.goto_functions.function_map.find(f_id);

  if(f_it==abstract_model.goto_functions.function_map.end())
    return;

  if(recursion_stack.find(f_id)!=recursion_stack.end())
  {
    message.warning("Ignoring recursive call to `" + f_id.as_string() + "'.");
    return;
  }
  else
    recursion_stack.insert(f_id);

  abstract_programt &abstract_program=f_it->second.body;
  
  // first build target map
  // and do inlining
  typedef std::map<abstract_programt::const_targett, unsigned> target_mapt;
  target_mapt target_map;
  
  PC_map.reserve(PC_map.size()+abstract_program.instructions.size());
  
  unsigned last_PC;

  for(abstract_programt::instructionst::iterator
      i_it=abstract_program.instructions.begin();
      i_it!=abstract_program.instructions.end();
      i_it++)
  {
    unsigned PC=PC_map.size();
    PC_map.push_back(instructiont());
    instructiont &instruction=PC_map.back();
    instruction.original=i_it;
    target_map[i_it]=PC;
    last_PC=PC;

    // do function calls
    if(i_it->is_function_call())
    {
      // figure out what is called
      const code_function_callt &call=
        to_code_function_call(i_it->code.concrete_pc->code);
        
      if(call.function().id()!="symbol")
        throw "expected symbol as function argument";
        
      const symbol_exprt &symbol=to_symbol_expr(call.function());
      
      build(abstract_model, symbol.get_identifier(), recursion_stack);
    }
  }
  
  // 2nd run: do targets

  for(abstract_programt::instructionst::iterator
      i_it=abstract_program.instructions.begin();
      i_it!=abstract_program.instructions.end();
      i_it++)
  {
    unsigned PC=target_map[i_it];

    if(i_it->is_return()) // jump to end of function
    {
      PC_map[PC].targets.push_back(last_PC);
    }
    else
    {
      const abstract_programt::targetst &targets=i_it->targets;

      for(abstract_programt::targetst::const_iterator
          t_it=targets.begin();
          t_it!=targets.end();
          t_it++)
      {
        target_mapt::const_iterator m_it=target_map.find(*t_it);
        if(m_it==target_map.end()) throw "failed to find target";
      
        PC_map[PC].targets.push_back(m_it->second);
      }
    }
  }

  recursion_stack.erase(f_id);
}

