/*******************************************************************\
  
Module: Initial Abstraction

Author: Daniel Kroening

Date: June 2003
 
\*******************************************************************/

#include <assert.h>

#include "initial_abstraction.h"
#include "discover_predicates.h"
#include "canonicalize.h"

/*******************************************************************\

Function: initial_abstractiont::init_preds

  Inputs:

 Outputs:

 Purpose: generate initial set of predicates for a concrete program

\*******************************************************************/

void initial_abstractiont::init_preds(
  const namespacet &ns,
  predicatest &predicates, 
  const concrete_modelt &concrete_model)
{
  status("Calculating initial set of predicates");

  init_preds(ns, predicates, concrete_model.goto_functions);
}

/*******************************************************************\

Function: initial_abstractiont::init_preds

  Inputs:

 Outputs:

 Purpose: generate initial set of predicates for a concrete program

\*******************************************************************/

void initial_abstractiont::init_preds(
  const namespacet &ns,
  predicatest &predicates, 
  const goto_functionst &goto_functions)
{
  forall_goto_functions(it, goto_functions)
    init_preds(ns, predicates, it->second.body);
}

/*******************************************************************\

Function: initial_abstractiont::init_preds

  Inputs:

 Outputs:

 Purpose: generate initial set of predicates for a concrete program

\*******************************************************************/

void initial_abstractiont::init_preds(
  const namespacet &ns,
  predicatest &predicates, 
  const goto_programt &goto_program)
{
  // collect all properties
  for(goto_programt::instructionst::const_iterator 
      it=goto_program.instructions.begin();
      it!=goto_program.instructions.end();
      it++) 
    if(it->is_assert())
    {
      std::set<predicatet> new_predicates;
      discover_predicates(it->guard, new_predicates, ns);
      
      // we just take them all
      for(std::set<predicatet>::const_iterator
          p_it=new_predicates.begin();
          p_it!=new_predicates.end();
          p_it++)
        predicates.lookup(*p_it);
    }
}

/*******************************************************************\

Function: initial_abstractiont::init_preds

  Inputs:

 Outputs:

 Purpose: generate initial set of predicates for a concrete program

\*******************************************************************/

void initial_abstractiont::init_preds(
  const namespacet &ns,
  predicatest &predicates, 
  const std::vector<exprt> &initial_predicates,
  abstract_modelt &abstract_model)
{
  status("Using provided set of initial predicates");

  for(std::vector<predicatet>::const_iterator
      p_it=initial_predicates.begin();
      p_it!=initial_predicates.end();
      p_it++)
  {
    bool negation;
    exprt p(*p_it);
    canonicalize(p, negation, ns);
    predicates.lookup(p);
  }
  
  // we add these _everywhere_
  
  abstract_functionst &functions=
    abstract_model.goto_functions;
    
  for(abstract_functionst::function_mapt::iterator
      f_it=functions.function_map.begin();
      f_it!=functions.function_map.end();
      f_it++)
  {
    abstract_programt &program=f_it->second.body;
  
    for(abstract_programt::instructionst::iterator
        i_it=program.instructions.begin();
        i_it!=program.instructions.end();
        i_it++)
    {
      for(unsigned p=0; p<predicates.size(); p++)
      {
        i_it->code.transition_relation.from_predicates.insert(p);
        i_it->code.transition_relation.to_predicates.insert(p);
      }
    }
  }
}

/*******************************************************************\

Function: initial_abstractiont::build_control_flow

  Inputs:

 Outputs:

 Purpose: compute abstraction according to set of predicates

\*******************************************************************/

void initial_abstractiont::build_control_flow(
  const goto_programt &concrete_program,
  abstract_programt &abstract_program)
{
  abstract_program.clear();
  
  // Loop over program - 1st time collects targets

  // Definitions for mapping between concrete and abstract instructions  
  typedef std::map<goto_programt::const_targett,
                   abstract_programt::targett> targets_mappingt;

  targets_mappingt targets_mapping;

  forall_goto_program_instructions(it, concrete_program)
  {
    abstract_programt::instructionst::iterator new_abstract_instruction=
      abstract_program.add_instruction();

    targets_mapping[it]=new_abstract_instruction;

    // copy location
    new_abstract_instruction->location=it->location;

    // copy type
    new_abstract_instruction->type=it->type;

    // store concrete pc for convenience
    new_abstract_instruction->code.concrete_pc=it;

    // this will need to be abstracted
    new_abstract_instruction->code.re_abstract=true;
  }

  // Loop over program - 2nd time updates goto targets
  forall_goto_program_instructions(it, concrete_program)
  {
    if(it->is_goto() || it->is_start_thread())
    {
      targets_mappingt::iterator abst_it=targets_mapping.find(it);

      if(abst_it==targets_mapping.end())
        throw "abstractor: abstract instruction not found";

      for(goto_programt::instructiont::targetst::const_iterator
          t_it=it->targets.begin();
          t_it!=it->targets.end();
          t_it++)
      {
        targets_mappingt::iterator
          abst_target_it=targets_mapping.find(*t_it);

        if(abst_target_it==targets_mapping.end())
          throw "abstractor: abstract goto target not found";

        abst_it->second->targets.push_back(abst_target_it->second);
      }
    }
  }
  
  abstract_program.update();
}

/*******************************************************************\

Function: initial_abstractiont::build_control_flow

  Inputs:

 Outputs:

 Purpose: compute abstraction according to set of predicates

\*******************************************************************/

void initial_abstractiont::build_control_flow(
  const goto_functionst &concrete_functions,
  abstract_functionst &abstract_functions)
{
  forall_goto_functions(it, concrete_functions)
  {
    const goto_functionst::goto_functiont &f=it->second;
    abstract_functionst::goto_functiont &a=
      abstract_functions.function_map[it->first];
    
    if(!a.body.empty()) continue; // has been done already

    a.body_available=f.body_available;
    a.type=f.type;

    if(f.body_available)
      build_control_flow(f.body, a.body);
  }
}

