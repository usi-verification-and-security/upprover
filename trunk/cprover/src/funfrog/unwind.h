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
    return (!unwindt::is_default_max_unwind(max_unwind)) &&
           unwind >= max_unwind;
  }

  bool is_recursion_unwinding(unsigned max_unwind, irep_idt target_function)
  {
    unsigned unwind = rec_unwind[target_function];
    return unwindt::is_default_max_unwind(max_unwind) &&
           unwind > 0;
  }
  
private:
  std::map<irep_idt, unsigned> rec_unwind;
  
  /* KE: max_unwind can be 0, -1 or 4294967295, or other default value marking
   * the user didn't set any value for --unwind 
   */
  static bool is_default_max_unwind(unsigned max_unwind) 
  {
      return (max_unwind == 0 || max_unwind == 4294967295 || max_unwind == (-1));
  } 
public:
  static std::string getWarningMessageForUnwondedCode(unsigned in_param) {
    if (unwindt::is_default_max_unwind(in_param)) return "";
      
    return "Warning: Result holds **ONLY** in this bound (!) "
            "Initial unwinding bound: " + std::to_string(in_param);
  }
};

#endif

