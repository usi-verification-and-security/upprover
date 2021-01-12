CProver update version 5.12 from https://github.com/diffblue/cbmc/tree/cbmc-5.12 
Date: Jan 2021

SA's approach for update:
1- Replace hifrog/trunk/cprover/src with cbmc5.12/cbmc/src

2- Re-organize CMakeLists.txt scripts in the root, i.e.,  cprover/CMakeLists.txt as well as sub-directories. You may do git diff for each script and revert back the important parts with preserving the changes. For e.g., change 'CBMC_SOURCE_DIR' —> 'PROJECT_SOURCE_DIR', change the project name to hifrog, etc.

3- Once CMakeLists.txt scripts are done, run make .. to make sure configs are complete.

4- goto /hifrog/trunk/cprover/src/funfrog and check each cpp file in IDE if it's compatible with the new CProver. Fix the compilation errors!

5- If you end up with a compilation error that no idea how to fix, go to https://github.com/diffblue/cbmc/ to the proper tag and search for the keyword in the repository to understand the corresponding change.
----------------------------------
File Changed in CProver's code:
=============
1- /cprover/src/util/arith_tools.h/cpp --> Bring back the method 'bool to_integer(const exprt &expr, mp_integer &int_value)' since UpProver's diff-checker needs that.

2- goto_symex directory : change static method'construct_get_goto_function' expose them for HiFrog/UpProver
  goto_symext::get_goto_functiont construct_get_goto_function(const goto_functionst &goto_functions);
void goto_symex_statet::get_l1_name(exprt &expr) const;

3-
goto-symex/goto_symex_state.cpp  removed static keyword from the function in goto_symex_state and exposed it in the interface of goto_symex_state. 
  static void get_l1_name(exprt &expr) --> public --> void goto_symex_statet::get_l1_name(exprt &expr) const

4- make a private method as public symex_assignt::assign_symbol


5- goto-symex/goto_symex.h.  Removed const keyword : symex_configt symex_config;  

----------------------------------
Some important git diff from CBMC code
guard_manager was introduced and passed around: https://github.com/diffblue/cbmc/commit/9727c5e7e8a1c955eab3d223072c640f3999e406#diff-07477ab2043ca50e9519eddde596c81003af7793419ef75d280ac22ce4d4bfc0

Use sharing_mapt to store propagation map: https://github.com/diffblue/cbmc/commit/32dc6d63e97106476d035feab7a010ec1d12b925

    if(p_it != propagation.end()) --> if(p_it.has_value())
          expr=p_it->second;   --> expr = *p_it;  
        
          
Remove definition of propagationt: https://github.com/diffblue/cbmc/commit/dd3dcc1b25201b73477d759ae9491480816596ec
Rename current_count method to latest_index: https://github.com/diffblue/cbmc/commit/228e765ceccb97d0c3c35b3a6c72a981645c1b13

get_unsigned_int was deprecated. Use get_size_t instead.  


 typedef std::map<irep_idt, std::pair<ssa_exprt, unsigned> > current_namest;
    current_namest current_names;  --> has changed to -->
using symex_renaming_levelt =
  sharing_mapt<irep_idt, std::pair<ssa_exprt, std::size_t>>;

---------------------------------------------------------------------
=====================================================================
---------------------------------------------------------------------
CBMC Version 5.10 from Git dev - 64-bit version (CBMC version 5.8 64-bit x86_64 linux)
Date: 22/08/2018

File Changed:
------------
- trunk/cprover/src/solvers/prop/prop_conv.h (move to public: propt &prop; // KE: change for hifrog)
- trunk/cprover/src/goto-symex/goto_symex.h (set virtual phi_function method) + declare constuct_get_goto_function method
- trunk/cprover/src/goto-symex/goto_symex_state.h (Move a method to public - get_l1_name() + try to remove dirty class, unless till stable!)
- trunk/cprover/src/goto-symex/goto_symex_state.cpp // Fix to ignor issues of parallel MC (two locations) + KE: remove dirty analysis
- trunk/cprover/src/goto-symex/syme_main.cpp // goto_symext::get_goto_functiont goto_symext::constuct_get_goto_function // to allow out symex to work//modified version of goto_symext::get_goto_functiont get_function_from_goto_functions.
- trunk/cprover/src/goto-symex/symex_function_call.cpp // Add assert(0) - bool goto_symext::get_unwind_recursion, as long as the return is false.
- trunk/cprover/src/cbmc/symex_bmc.cpp (remove debug massege to show progress: void symex_bmct::symex_step).
- trunk/cprover/src/util/expr.h/.cpp - add a function — I will need to add functions from old source to new one (those functions are created by the team and needed)
- Remove dirty - once found

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
                 

