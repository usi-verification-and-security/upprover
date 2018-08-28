/* 
 * File:   symex_assertion_no_partitiont.cpp
 * Author: karinek
 * 
 * Created on 20 April 2017, 17:51
 */
#include "symex_no_partition.h"

#include <util/expr_util.h>
#include <goto-symex/goto_symex_state.h>
#include <goto-symex/symex_slice_class.h>
#include <funfrog/assertion_info.h>
#include <util/time_stopping.h>
#include "smt_symex_target_equation.h"


bool symex_no_partitiont::prepare_SSA(const assertion_infot &assertion, const goto_functionst& goto_functions)
{
  current_assertion = &assertion;

  // these are quick...
  if(assertion.is_trivially_true())
  {
    status() << "ASSERTION IS TRUE" << log.eom;
    return true;
  }
  
  // Clear the state
  state = goto_symext::statet();


  // Old: ??? state.value_set = value_sets;
  state.source.pc = goto_program.instructions.begin();
  
  loc = 0;
  return process_planned(state, goto_functions, false); // In it, in the end need to call convert
}



bool symex_no_partitiont::refine_SSA(const assertion_infot &assertion, bool force_check)
{
    // TODO
    return false;
}

bool symex_no_partitiont::process_planned(statet &state, const goto_functionst &goto_functions, bool force_check)
{
    // Proceed with symbolic execution
    absolute_timet before, after;
    before=current_time();

    // Taken from bmc.cpp (main)
    try
    {
        // perform symbolic execution
        this->operator () (state, goto_functions, goto_program);

        // add a partial ordering, if required
        if(equation.has_threads())
        {
            error () << "No support for threads. Exit." << log.eom;
            exit(0);
        }
    }
    catch(const std::string &error_str)
    {
        messaget message(log.get_message_handler());
        message.error() << error_str << messaget::eom;

        assert(0);
    }
    catch(const char *error_str)
    {
        messaget message(log.get_message_handler());
        message.error() << error_str << messaget::eom;

        assert(0);
    }
    catch(std::bad_alloc)
    {
        error() << "Out of memory" << log.eom;
        assert(0);
    }

    statistics() << "size of program expression: "
                 << equation.SSA_steps.size()
                 << " steps" << log.eom;


    after=current_time();

    status() << "SYMEX TIME: " << (after-before) << log.eom;

    if(remaining_vccs!=0 || force_check)
    {
        if (use_slicing) {
          before=current_time();
            status() << "All SSA steps: " << equation.SSA_steps.size() << log.eom;
            symex_slicet symex_slice;
            symex_slice.slice(equation);
            status() << "Ignored SSA steps after slice: " << equation.count_ignored_SSA_steps() << log.eom;
            after=current_time();
            status() << "SLICER TIME: " << (after-before) << log.eom;
        }
    } else {
        status() << "Assertion(s) hold trivially(.)" << log.eom;
        return true;
    }
    return false;
}

bool symex_no_partitiont::get_unwind(const symex_targett::sourcet & source, unsigned unwind) {
    // returns true if we should not continue unwinding
    // for support of different bounds in different loops, see how it's done in symex_bmct
    return unwind >= max_unwind;
}

symex_no_partitiont::symex_no_partitiont(const namespacet & _ns, symbol_tablet & _new_symbol_table,
                                         hifrog_symex_target_equationt & _target, message_handlert & _message_handler,
                                         const goto_programt & _goto_program, bool _use_slicing)
 :
    goto_symext(_message_handler, _ns, _new_symbol_table, _target),
            equation(_target),
            goto_program(_goto_program),
            current_assertion(nullptr),
            loc(0),
            use_slicing(_use_slicing)
    {}


