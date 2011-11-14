/*******************************************************************

 Module: Information about an assertion to be checked, i.e., its
 location in the code and a call_stack as a path to it (it is 
 unique as long as there are no loops in the analyzed code).

 Author: Ondrej Sery

\*******************************************************************/

#ifndef CPROVER_ASSERTION_INFO_H
#define CPROVER_ASSERTION_INFO_H

#include <loopfrog/call_stack.h>

// Unique identification of an assertion to be checked
class assertion_infot {
public:
  assertion_infot() : matching_type(ANY), target_stack(NULL) {}
          
  assertion_infot(const goto_programt::const_targett& _location):
          matching_type(ASSERT_GROUPING), target_stack(NULL), 
          location(_location) {}
          
  assertion_infot(const call_stackt& _target_stack,
          const goto_programt::const_targett& _location):
          matching_type(NO_ASSERT_GROUPING), target_stack(&_target_stack), 
          location(_location) {}

  const call_stackt& get_target_stack() const {
    assert(matching_type == NO_ASSERT_GROUPING); 
    return *target_stack;
  }
  const goto_programt::const_targett& get_location() const {
    assert(matching_type != ANY); 
    return location;
  }
  bool is_trivially_true() const {
    if (matching_type == ANY)
      return false;
    return location->guard.is_true();
  }
  
  // Does the call stack match the current stack? If we group all assertions
  // regardless the stack, this just returns the same value as the parent stack 
  // frame.
  bool stack_matches(const irep_idt& function_id, unsigned depth,
        bool parent_stack_matches) const
  {
    if (matching_type != NO_ASSERT_GROUPING)
      return parent_stack_matches;
  
    bool stack_matches = parent_stack_matches && 
        (depth < get_target_stack().size());

    // Does the callstack prefix match callstack of the assertion to be checked
    if (stack_matches) {
      const code_function_callt &call =
        to_code_function_call(to_code(get_target_stack().at(depth)->code));
      const irep_idt &ass_stack_call_id = call.function().get("identifier");
      
      stack_matches = ass_stack_call_id == function_id;
    }
  
    return stack_matches;
  }

  // Does the given assertion match the one to be currently analyzed?
  bool assertion_matches(unsigned depth, 
          const goto_programt::const_targett& current_assertion) const
  {
    switch (matching_type) {
      case NO_ASSERT_GROUPING:
        if (depth != get_target_stack().size())
          return false;
      case ASSERT_GROUPING:
        if (get_location() != current_assertion)
          return false;
      default:
        return true;
    }
  }

  bool is_assert_grouping() const
  {
    if (matching_type == NO_ASSERT_GROUPING){
      return false;
    } else {
      return true;
    }
  }

  bool is_all_assert() const
  {
    if (matching_type == ANY){
      return true;
    } else {
      return false;
    }
  }

private:
  typedef enum {ANY, ASSERT_GROUPING, NO_ASSERT_GROUPING} matching_typet;
  
  matching_typet matching_type;
  const call_stackt* target_stack;
  goto_programt::const_targett location;
};

#endif

