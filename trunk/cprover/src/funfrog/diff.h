#include <time_stopping.h>
#include <goto-programs/read_goto_binary.h>

#include "arith_tools.h"
#include "fixedbv.h"
#include "ieee_float.h"
#include <cstring>
#include <iostream>
#include <fstream>

class difft {
public:
  bool do_diff(goto_functionst &goto_functions_1, goto_functionst &goto_functions_2, const char* file3);

  
private:
  std::vector<std::pair<const irep_idt*, bool> > functions;

  bool is_untouched(const irep_idt &name);

  bool unroll_goto(goto_functionst &goto_functions, const irep_idt &name,
        std::vector<std::pair<std::string, unsigned> > &goto_unrolled, unsigned init, bool inherit_change);

};

