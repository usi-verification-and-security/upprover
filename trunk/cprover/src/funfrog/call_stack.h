/*******************************************************************

 Module: Call Stacks

 Author: CM Wintersteiger

 \*******************************************************************/

#ifndef _CPROVER_LOOPFROG_CALL_STACK_H_
#define _CPROVER_LOOPFROG_CALL_STACK_H_

#include <deque>
#include <goto-programs/goto_program.h>

// we want a stack... but we also want iterators...

class call_stackt : public std::deque<goto_programt::const_targett> 
{
public:
  void push(const goto_programt::const_targett &item)
  {
    push_back(item);
  }
  
  void pop(void)
  {
    pop_back();
  }
  
  goto_programt::const_targett& top(void)
  {
    return back();
  }
  
};

#endif /*_CPROVER_LOOPFROG_CALL_STACK_H_*/
