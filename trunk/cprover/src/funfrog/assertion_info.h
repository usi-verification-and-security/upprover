/*******************************************************************

 Module: Information about an assertion to be checked, i.e., its
 location in the code and a call_stack as a path to it (it is 
 unique as long as there are no loops in the analyzed code).

 Author: Ondrej Sery

\*******************************************************************/

#ifndef ASSERTION_INFO_H_
#define ASSERTION_INFO_H_

#include <loopfrog/call_stack.h>

// Unique identification of an assertion to be checked
class assertion_infot {
public:
  assertion_infot(const call_stackt& _target_stack,
          const goto_programt::const_targett& _location):
          target_stack(_target_stack), location(_location) {}

  const call_stackt& get_target_stack() const {return target_stack;}
  const goto_programt::const_targett& get_location() const {return location;}

private:
  const call_stackt& target_stack;
  goto_programt::const_targett location;
};

#endif /*ASSERTION_INFO_H_*/

