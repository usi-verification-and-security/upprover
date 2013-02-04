#ifndef CPROVER_UNWIND_H
#define CPROVER_UNWIND_H

class unwindt{
protected:

  void increment_unwinding_counter(irep_idt target_function){
    rec_unwind[target_function]++;
  }

  void decrement_unwinding_counter(irep_idt target_function){
    rec_unwind[target_function]--;
  }

  bool is_unwinding_exceeded(unsigned max_unwind, irep_idt target_function)
  {
    unsigned unwind = rec_unwind[target_function];
    return max_unwind != 0 &&
           unwind >= max_unwind;
  }

  bool is_recursion_unwinding(unsigned max_unwind, irep_idt target_function)
  {
    unsigned unwind = rec_unwind[target_function];
    return max_unwind == 0 &&
           unwind > 0;
  }

private:
  std::map<irep_idt, unsigned> rec_unwind;
};

#endif
