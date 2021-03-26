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
1- src/solvers/prop/prop_conv_solver.h  move to public: propt &prop; 
 
3- goto-symex/goto_symex_state.cpp  remove static keyword from get_l1_name as follows:
//static void get_l1_name(exprt &expr){...}
void goto_symex_statet::get_l1_name(exprt &expr) const
{...}
goto-symex/goto_symex_state.h move the method to public to expose it for HiFrog/UpProver: 
void goto_symex_statet::get_l1_name(exprt &expr) const;

4- goto-symex/symex_main.cpp  following previous hacks add :

goto_symext::get_goto_functiont goto_symext::construct_get_goto_function( //hkd!
        const goto_functionst &goto_functions)
{
    return [&goto_functions](
            const irep_idt &key) -> const goto_functionst::goto_functiont & {
        return goto_functions.function_map.at(key);
    };
}

 and in goto-symex/goto_symex.h declare construct_get_goto_function method
 //Non-static method for HiFrog/UpProver
 goto_symext::get_goto_functiont construct_get_goto_function(const goto_functionst &goto_functions);


5- symex_assign.h Make a private method as public   void symex_assign_symbol(...);

6- goto-symex/goto_symex.h  Removed const keyword : symex_configt symex_config;  

7- src/goto-checker/symex_bmc.h (remove debug massege to show progress: void symex_bmct::symex_step).

8- goto_symex_state.cpp Remove #include <analyses/dirty.h> Remove dirty check and fix issue in the affected methods in the following files: 
  cprover/src/goto-symex/goto_symex_state.cpp     
  cprover/src/goto-symex/symex_decl.cpp           
  cprover/src/goto-symex/symex_function_call.cpp  
  cprover/src/goto-symex/symex_goto.cpp           
  cprover/src/goto-symex/symex_main.cpp 

9- src/util/arith_tools.h/cpp  Bring back the method 'bool to_integer(const exprt &expr, mp_integer &int_value)' since UpProver's diff-checker needs that.

10 - cprover 5.11
goto-symex/renaming_level.h
removed static method increase_counter and undo the changes in
  //https://github.com/diffblue/cbmc/commit/e71ca91c9eeaaa8dda70f18ffb7d2bcea574035d
  This undong has been pushed as SHA 34bfa974 in upprover

11- Remove deprecated exprt::make_true(). As suggested use true_exprt() instead. 

12 src/goto-symex/goto_symex_state.cpp: fix an unitialized variable reported by valgrind(commit:835509cc) 
changed the c'tor goto_symex_statet() and added the following:
  +  run_validation_checks = false;
  +  has_saved_jump_target = false;
  +  has_saved_next_instruction = false;
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

Remove unused case of return assignment in symex (unresolved in hifrog yet)
https://github.com/diffblue/cbmc/commit/7dc47a4c6681ea61b562e3ad7edb96a3f55e5034 


in symect_assertion_sum.cpp
  // get the current L2 version of the L1 symbol
 //state.rename(expr, ns); deprecated
  use the following:
  exprt res = state.rename<L2>(expr, ns).get();
  to_ssa_expr(res);

---------------------------------------------------------------------
cprover 5.30
prop_conv_solver.h   propt &prop; moved to public



=====================================================================
---------------------------------------------------------------------
CBMC Version 5.10 from Git dev - 64-bit version (CBMC version 5.8 64-bit x86_64 linux)
Date: 22/08/2018

File Changed:
------------
- trunk/cprover/src/solvers/prop/prop_conv.h (move to public: propt &prop; // KE: change for hifrog)
- trunk/cprover/src/goto-symex/goto_symex.h (set virtual phi_function method) + declare construct_get_goto_function method
- trunk/cprover/src/goto-symex/goto_symex_state.h (Move a method to public - get_l1_name() + try to remove dirty class, unless till stable!)
- trunk/cprover/src/goto-symex/goto_symex_state.cpp // Fix to ignor issues of parallel MC (two locations) + KE: remove dirty analysis

- trunk/cprover/src/goto-symex/symex_main.cpp // goto_symext::get_goto_functiont goto_symext::constuct_get_goto_function // to allow out symex to work //modified version of goto_symext::get_goto_functiont get_function_from_goto_functions.

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
                 

