/*******************************************************************\

Module: The abstract program

Author: Daniel Kroening

Date: January 2004

\*******************************************************************/

#include <bplang/expr2bp.h>

#include "abstract_program.h"

/*******************************************************************\

Function: abstract_programt::output_other_instruction

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::ostream& abstract_programt::output_instruction(
  const namespacet &ns,
  const irep_idt &identifier,
  std::ostream &out,
  const_targett it) const
{
  if(!it->location.is_nil())
    out << "        // " << it->location.as_string() << "\n";
  else
    out << "        // no location\n";

  out << "From predicates:";
  for(std::set<unsigned>::const_iterator
      p_it=it->code.transition_relation.from_predicates.begin();
      p_it!=it->code.transition_relation.from_predicates.end();
      p_it++)
    out << " " << *p_it;
  
  out << std::endl;

  out << "        ";
  out << "To predicates:";
  for(std::set<unsigned>::const_iterator
      p_it=it->code.transition_relation.to_predicates.begin();
      p_it!=it->code.transition_relation.to_predicates.end();
      p_it++)
    out << " " << *p_it;
  
  out << std::endl;

  if(!it->labels.empty())
  {
    out << "        // Labels:";
    for(instructiont::labelst::const_iterator
        l_it=it->labels.begin();
        l_it!=it->labels.end();
        l_it++)
    {
      out << " " << *l_it;
    }
    
    out << std::endl;
  }

  if(it->is_target())
    out << std::setw(6) << it->target_number << ": ";
  else
    out << "        ";

  switch(it->type)
  {
  case NO_INSTRUCTION_TYPE:
    out << "NO INSTRUCTION TYPE SET" << std::endl;
    break;
  
  case GOTO:
    if(!it->guard.is_true())
    {
      out << "IF "
          << from_expr(ns, identifier, it->guard)
          << " THEN ";
    }

    out << "GOTO ";
    
    for(instructiont::targetst::const_iterator
        gt_it=it->targets.begin();
        gt_it!=it->targets.end();
        gt_it++)
    {
      if(gt_it!=it->targets.begin()) out << ", ";
      out << (*gt_it)->target_number;
    }
      
    out << std::endl;
    break;
    
  case RETURN:
  case OTHER:
  case DECL:
  case FUNCTION_CALL:
  case ASSIGN:
    {
      #if 0
      for(symex_equationt::equationt::premisest::const_iterator
          p_it=it->code.equation.assignments.begin();
          p_it!=it->code.equation.assignments.end();
          p_it++)
        out << from_expr(ns, identifier, *p_it) << std::endl;
      #endif

      out << "        ";
      out << "Changed predicates:";

      for(abstract_transition_relationt::valuest::const_iterator
          p_it=it->code.transition_relation.values.begin();
          p_it!=it->code.transition_relation.values.end();
          p_it++)
        out << " " << p_it->first;

      out << std::endl;

      out << "        ";
      out << "Constraints: ";         

      for(abstract_transition_relationt::constraintst::const_iterator
          e_it=it->code.transition_relation.constraints.begin();
          e_it!=it->code.transition_relation.constraints.end();
          e_it++)
      {
        const exprt &constraint=*e_it;

        if(e_it!=it->code.transition_relation.constraints.begin())
          out << "             ";

        out << expr2bp(constraint) << std::endl;
      }
      
      out << std::endl;

      return out;
    }
    break;
    
  case ASSUME:
  case ASSERT:
    if(it->is_assume())
      out << "ASSUME ";
    else
      out << "ASSERT ";
      
    {
      out << from_expr(ns, identifier, it->guard);
    
      const irep_idt &comment=it->location.get("comment");
      if(comment!="") out << " // " << comment;
    }
      
    out << std::endl;
    break;
    
  case SKIP:
    out << "SKIP" << std::endl;
    break;
    
  case END_FUNCTION:
    out << "END_FUNCTION" << std::endl;
    break;
    
  case LOCATION:
    out << "LOCATION" << std::endl;
    break;
    
  case DEAD:
    out << "DEAD" << std::endl;
    break;
    
  case ATOMIC_BEGIN:
    out << "ATOMIC_BEGIN" << std::endl;
    break;
    
  case ATOMIC_END:
    out << "ATOMIC_END" << std::endl;
    break;
    
  case START_THREAD:
    out << "START THREAD ";

    if(it->targets.size()==1)
      out << it->targets.front()->target_number;
    
    out << std::endl;
    break;
    
  case END_THREAD:
    out << "END THREAD" << std::endl;
    break;
    
  default:
    throw "unknown statement";
  }

  return out;  
}

/*******************************************************************\

Function: operator<

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool operator<(const abstract_programt::const_targett i1,
               const abstract_programt::const_targett i2)
{
  const abstract_programt::instructiont &_i1=*i1;
  const abstract_programt::instructiont &_i2=*i2;
  return &_i1<&_i2;
}
