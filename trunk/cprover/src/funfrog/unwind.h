#ifndef CPROVER_UNWIND_H
#define CPROVER_UNWIND_H

class unwindt{
protected:
  unwindt(unsigned int max_unwind) : max_unwind{max_unwind} {}

  void increment_unwinding_counter(irep_idt target_function){
    rec_unwind[target_function]++;     //if the key is not found in rec_unwind,  it inserts a new pair with that key
                                       // and a default value 0 and returns a reference to it. Then we increment its value.
  
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

