CBMC Version 5.6 from Git - 64-bit version
Date: 15/11/2016

File Changed:
=============
- trunk/cprover/src/solvers/prop/prop_conv.h
- trunk/cprover/src/goto-symex/goto_symex_state.h
- trunk/cprover/src/config.inc
- trunk/cprover/src/goto-symex/goto-symex.h (set virtual phi_function method)

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


