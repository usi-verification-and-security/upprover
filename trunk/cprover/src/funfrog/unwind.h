#ifndef CPROVER_UNWIND_H
#define CPROVER_UNWIND_H

class unwindt{
protected:
  std::map<locationt, unsigned> rec_unwind;

  bool get_unwind_rec(unsigned unwind, unsigned max_unwind)
  {
    return max_unwind!=0 &&
           unwind>=max_unwind;
  };
};

#endif
