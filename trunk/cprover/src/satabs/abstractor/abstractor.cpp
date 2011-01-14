/*******************************************************************\

Module: Abstractor (generates abstract program given a set of predicates)

Author: Daniel Kroening
        Karen Yorav 

  Date: June 2003

\*******************************************************************/

#include <map>

#include <simplify_expr.h>
#include <find_symbols.h>

#include <langapi/language_util.h>

#include "abstractor.h"
#include "abstract_expression.h"

/*******************************************************************\

Function: abstractort::abstract_variables

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void abstractort::abstract_variables(
  const predicatest &predicates,
  abstract_modelt::variablest &variables)
{
  variables.resize(predicates.size());

  for(unsigned i=0; i<predicates.size(); i++)
  {
    variables[i].description=
      from_expr(concrete_model.ns, "", predicates[i]);

    // remove line breaks
    for(unsigned j = 0; j<variables[i].description.size(); j++)
      if(variables[i].description[j]=='\n' ||
         variables[i].description[j]=='\r')
        variables[i].description[j]=' ';

    // local or global?
    variables[i].var_class=get_var_class(predicates[i]);
  }
}

/*******************************************************************\

Function: abstractort::get_var_class

  Inputs:

 Outputs:

 Purpose: computes the thread-category of the abstract variable

\*******************************************************************/

abstract_modelt::variablet::var_classt abstractort::get_var_class(
  const predicatet &predicate)
{
  // get list of symbols in the predicate

  typedef hash_set_cont<irep_idt, irep_id_hash> symbolst;
  symbolst symbols;

  find_symbols(predicate, symbols);

  // is there a global variable in there?
  
  bool found_shared_global=false,
       found_thread_local=false;

  for(symbolst::const_iterator it=symbols.begin();
      it!=symbols.end();
      it++)
  {
    const symbolt &symbol=concrete_model.ns.lookup(*it);
    if(symbol.static_lifetime) // global?
    {
      if(symbol.thread_local)
        found_thread_local=true;
      else
        found_shared_global=true;
    }
  }

  #if 0
  return found_shared_global?
           abstract_modelt::variablet::SHARED_GLOBAL:
         found_thread_local?
           abstract_modelt::variablet::THREAD_LOCAL:
           abstract_modelt::variablet::PROCEDURE_LOCAL;
  #else
  // HACK FOR ALEXANDER. WILL EVENTUALLY REVERT TO THE ABOVE
  return found_shared_global?
           abstract_modelt::variablet::SHARED_GLOBAL:
           abstract_modelt::variablet::PROCEDURE_LOCAL;
  #endif
}

/*******************************************************************\

Function: abstractort::build_abstraction

  Inputs:

 Outputs:

 Purpose: compute abstraction according to set of predicates

\*******************************************************************/

void abstractort::build_abstraction(const predicatest &predicates)
{
  // new predicates?
  have_new_predicates=(predicates!=old_predicates);
  old_predicates=predicates;
  
  status("Computing Predicate Abstraction for Program");

  // define abstract variables
  abstract_variables(predicates, abstract_model.variables);

  forall_goto_functions(c_it, concrete_model.goto_functions)
  {
    const goto_functionst::goto_functiont &f=c_it->second;

    abstract_functionst::goto_functiont &a=
      abstract_model.goto_functions.function_map[c_it->first];

    if(f.body_available)
      build_abstraction(predicates, f.body, a.body);
  }
}

/*******************************************************************\

Function: abstractort::build_abstraction

  Inputs:

 Outputs:

 Purpose: compute abstraction according to set of predicates

\*******************************************************************/

void abstractort::build_abstraction(
  const predicatest &predicates, 
  const goto_programt &goto_program,
  abstract_programt &abstract_program)
{
  // this needs to be done every time: the abstract guards
  // and the abstract transition relation depend on the predicates

  abstract_programt::instructionst::iterator a_it=
    abstract_program.instructions.begin();

  for(goto_programt::instructionst::const_iterator 
      c_it=goto_program.instructions.begin();
      c_it!=goto_program.instructions.end();
      c_it++, a_it++)
  {
    // only do it if marked 're-abstract', or we have to
    if(!have_new_predicates &&
       !a_it->code.re_abstract) continue;

    a_it->code.re_abstract=false;

    print(9, "Abstracting "+c_it->location.as_string());

    switch(c_it->type)
    {
    case GOTO:
    case ASSERT:
    case ASSUME:
      // if its a goto/assume/assert abstract the guard
      a_it->guard=c_it->guard;
      abstract_expression(predicates, a_it->guard, concrete_model.ns);
      break;

    case ASSIGN:
      pred_abstract_block(
        c_it,
        predicates,
        a_it->code.transition_relation);
      break;

    case OTHER:
    case DECL:
      if(c_it->code.is_nil())
        a_it->code.transition_relation.clear();
      else
      {
        pred_abstract_block(
          c_it,
          predicates,
          a_it->code.transition_relation);
      }
      break;

    case DEAD:
    case SKIP:
    case START_THREAD:
    case END_THREAD:
    case END_FUNCTION:
    case LOCATION:
    case ATOMIC_BEGIN:
    case ATOMIC_END:
      // nothing
      break;

    case FUNCTION_CALL:
      // for now, we don't have arguments
      break;

    case RETURN:
      // for now, we don't have return values
      break;

    default:
      throw "unexpected instruction";
    }
  }
}

/*******************************************************************\

Function: abstractort::get_value

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

exprt abstractort::get_value(
  unsigned p_nr,
  const predicatest &predicates,
  const exprt &value)
{
  if(value.is_constant()) return value;

  exprt dest;
  dest.make_nil();

  // previous predicate?
  for(unsigned i=0; i<predicates.size(); i++)
  {
    #if 0
    contextt context;
    const namespacet ns(context);
    std::cout << "V " << p_nr << " " << from_expr(ns, "", value) << std::endl;
    std::cout << "P " << i << " " << from_expr(ns, "", predicates[i]) << std::endl;
    #endif
  
    if(value==predicates[i])
    {
      dest=exprt("predicate_symbol", typet("bool"));
      dest.set("identifier", i);
      break;
    }
  }
  
  return dest;
}
