CBMC Version 5.6 from Git - 64-bit version (CBMC version 5.6 64-bit x86_64 linux)
Date: 20/01/2017

File Changed:
=============
- trunk/cprover/src/solvers/prop/prop_conv.h (move to public: propt &prop; // KE: change for hifrog)
- trunk/cprover/src/goto-symex/goto_symex_state.h (Move a method to public - get_l1_name())
- trunk/cprover/src/goto-symex/goto_symex.h (set virtual phi_function method)
- trunk/cprover/src/goto-symex/symex_decl.cpp (remove dirty analysis code)
- trunk/cprover/src/config.inc (change: add ../ to minisat2 path)
- trunk/cprover/src/Makefile
- trunk/cprover/src/goto-symex/goto_symex_state.cpp // Fix to ignor issues of parallel MC
- trunk/cprover/util/expr.h/.cpp - add a function

minisat-2.2.1:
==============
run "patch -p1 < ../scripts/minisat-2.2.1-patch"
It shall modify the following files:
trunk/minisat-2.2.1/minisat/core/Solver.cc
trunk/minisat-2.2.1/minisat/core/SolverTypes.h
trunk/minisat-2.2.1/minisat/mtl/IntTypes.h
trunk/minisat-2.2.1/minisat/mtl/Vec.h
trunk/minisat-2.2.1/minisat/simp/SimpSolver.cc
trunk/minisat-2.2.1/minisat/utils/Options.h
trunk/minisat-2.2.1/minisat/utils/ParseUtils.h

Taken from Git:
===============
https://github.com/diffblue/cbmc
(found by git remote show origin)

Special modifications in HiFrog:
================================
- symex_assertion_sum.h: Phi and vcc methods are virtual.
- To public: get_l1_name
  // only required for value_set.assign
  void get_l1_name(exprt &expr) const; // KE: changes for hifrog
-- expr.h add function:
  const std::string print_number_2smt() const; // hckd!!
-- expr.cpp add function impl


