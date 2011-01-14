/*******************************************************************\

Module: The Abstract Model

Author: Daniel Kroening
        Karen Yorav 

Date: June 2003

\*******************************************************************/

#ifndef CPROVER_CEGAR_ABSTRACT_MODEL_H
#define CPROVER_CEGAR_ABSTRACT_MODEL_H

#include "abstract_transition_relation.h"
#include "abstract_program.h"

class abstract_modelt
{
public:
  // abstract program
  abstract_functionst goto_functions;
  
  // variables
  struct variablet
  {
    std::string description;
    
    // the threading category
    enum var_classt { NONE, SHARED_GLOBAL, THREAD_LOCAL, PROCEDURE_LOCAL };
    var_classt var_class;
    
    bool is_shared_global() const { return var_class==SHARED_GLOBAL; }
    bool is_thread_local() const { return var_class==THREAD_LOCAL; }
    bool is_procedure_local() const { return var_class==PROCEDURE_LOCAL; }
    
    // if local, which function?
    typedef std::set<irep_idt> functionst;
    functionst functions;
    
    variablet():var_class(NONE)
    {
    }
  };

  typedef std::vector<variablet> variablest;
  variablest variables;
  
  abstract_modelt()
  {
  }
  
  void output(const namespacet &ns, std::ostream &out) const
  {
    goto_functions.output(ns, out);
  }
  
  // given a concrete location, returns the appropriate abstract one
  abstract_programt::targett get_abstract_location(
    goto_programt::const_targett concrete_location);
};

#endif
