CBMC Version 5.7 from Git - 64-bit version (CBMC version 5.8 64-bit x86_64 linux)
Date: 02/06/2017

File Changed:
=============
- trunk/cprover/src/solvers/prop/prop_conv.h (move to public: propt &prop; // KE: change for hifrog)
- trunk/cprover/src/goto-symex/goto_symex.h (set virtual phi_function method)
- trunk/cprover/src/goto-symex/goto_symex_state.h (Move a method to public - get_l1_name() + try to remove dirty class, unless till stable!)
- trunk/cprover/src/goto-symex/goto_symex_state.cpp // Fix to ignor issues of parallel MC (two locations) + KE: remove dirty analysis
- trunk/cprover/src/goto-symex/symex_function_call.cpp // Add assert(0) - bool goto_symext::get_unwind_recursion, as long as the return is false.
- trunk/cprover/src/cbmc/symex_bmc.cpp (remove debug massege to show progress: void symex_bmct::symex_step).
- trunk/cprover/src/util/expr.h/.cpp - add a function — I will need to add functions from old source to new one (those functions are created by the team and needed)
- trunk/cprover/src/config.inc (change: add ../ to minisat2 path) —WE removed to CMAKE, therefore we do not need it anymore
- trunk/cprover/src/Makefile - WE removed to CMAKE, therefore we do not need it anymore - assure we don't override it with junk
- Remove dirty - where found

minisat-2.2.1:
==============
Shall be updated automatically with CMake. 
Error means you work with the old version.


Taken from Git:
===============
https://github.com/diffblue/cbmc
(found by git remote show origin)
http://www.cprover.org/svn/cbmc/trunk/COMPILING

Special modifications in HiFrog:
================================
- symex_assertion_sum.h: Phi and vcc methods are virtual. — we check the signature whether it is as the same as the super class
- To public: get_l1_name
  // only required for value_set.assign
  void get_l1_name(exprt &expr) const; // KE: changes for hifrog
- expr.h add function:
  const std::string print_number_2smt() const; // hckd!!
- expr.cpp add function impl
- Issues with dirty analysis
  - Removed from goto-symex/symex_main.cpp
                 goto-symex/goto_symex_state.cpp
                 goto-symex/goto_symex_state.h
                 goto-symex/symex_function_call.cpp
                 goto-symex/symex_goto.cpp
                 goto-symex/symex_decl.cpp
                 

