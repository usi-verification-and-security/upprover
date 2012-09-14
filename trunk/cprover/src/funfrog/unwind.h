#ifndef CPROVER_UNWIND_H
#define CPROVER_UNWIND_H

class unwindt{
protected:


  void set_function_to_be_unwound(irep_idt target_function){
    current_function = target_function;
  }

  void increment_unwinding_counter(){
    std::cout << "unwind " << current_function << " (" << rec_unwind[current_function] << ")\n";
    rec_unwind[current_function]++;
  }

  void decrement_unwinding_counter(){
    rec_unwind[current_function]--;
  }

  bool is_unwinding_exceeded(unsigned max_unwind)
  {
    unsigned unwind = rec_unwind[current_function];
    return max_unwind!=0 &&
           unwind>=max_unwind;
  };

private:
  std::map<irep_idt, unsigned> rec_unwind;

  irep_idt current_function;
};

#endif
