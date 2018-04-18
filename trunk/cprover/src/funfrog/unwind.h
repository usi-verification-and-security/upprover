#ifndef CPROVER_UNWIND_H
#define CPROVER_UNWIND_H

class unwindt{
protected:
  unwindt(unsigned int max_unwind) : max_unwind{max_unwind} {}

  void increment_unwinding_counter(irep_idt target_function){
    rec_unwind[target_function]++;
  }

  void decrement_unwinding_counter(irep_idt target_function){
    rec_unwind[target_function]--;
  }

  bool is_unwinding_exceeded(irep_idt target_function)
  {
    unsigned unwind = rec_unwind[target_function];
    return unwind > max_unwind;
  }

  bool is_recursion_unwinding(irep_idt target_function)
  {
    unsigned unwind = rec_unwind[target_function];
    return unwind > 0;
  }
  
private:
  std::map<irep_idt, unsigned> rec_unwind;
  unsigned int max_unwind;

};

#endif

