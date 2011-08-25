/*******************************************************************\

Module: Counterexamples

Author: Daniel Kroening
        Karen Yorav 

Date: June 2003

\*******************************************************************/

#ifndef CPROVER_CEGAR_ABSTRACT_STATE_H
#define CPROVER_CEGAR_ABSTRACT_STATE_H

#include <iostream>
#include <list>

#include "../abstractor/abstract_model.h"

/* An abstract state */
class abstract_stept
{
public:
  typedef enum { NONE, STATE, LOOP_BEGIN, LOOP_END } step_typet;
  step_typet step_type;

  abstract_stept(step_typet _step_type):
    step_type(_step_type),
    thread_nr(0),
    label_nr(0),
    has_pc(false),
    branch_taken(false),
    relevant(true)
  {
  }
  
  bool is_state() const { return step_type==STATE; }
  bool is_loop_begin() const { return step_type==LOOP_BEGIN; }  
  bool is_loop_end() const { return step_type==LOOP_END; }
  
  // this transition done by given thread number
  unsigned thread_nr;
  
  // this is the instruction that was executed to get into this state
  abstract_programt::targett pc;
  unsigned label_nr;

  // the first one has no PC
  bool has_pc;
  
  // the values visible to the thread
  typedef std::vector<bool> predicate_valuest;
  predicate_valuest predicate_values;

  // for goto
  bool branch_taken;
  
  friend std::ostream& operator<<(
    std::ostream& out,
    const abstract_stept &step);
    
  // loop detection
  unsigned loop_begin, loop_end;
  
  void output(std::ostream &out) const;
  
  // slicing
  bool relevant;
};

/* An abstract state */
class abstract_statet:public abstract_stept
{
public:
  abstract_statet():abstract_stept(STATE)
  {
  }
};

std::ostream& operator<<(
  std::ostream& out,
  const abstract_stept &state);

#endif
