/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

/* 
 * File:   symex_assertion_no_partitiont.cpp
 * Author: karinek
 * 
 * Created on 20 April 2017, 17:51
 */
#include <expr_util.h>
#include <goto-symex/goto_symex_state.h>
#include <goto-symex/symex_slice_class.h>

#include "symex_no_partition.h"

bool symex_no_partitiont::prepare_SSA(const assertion_infot &assertion, const goto_functionst& goto_functions)
{
  current_assertion = &assertion;

  // these are quick...
  if(assertion.is_trivially_true())
  {
    status() << "ASSERTION IS TRUE" << eom;
    return true;
  }

  // Start Checking:
  last_source_location.make_nil();
  
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
            error () << "No support for threads. Exit." << eom;
            exit(0);
        }
    }
    catch(const std::string &error_str)
    {
        messaget message(get_message_handler());
        message.error().source_location=last_source_location;
        message.error() << error_str << messaget::eom;

        assert(0);
    }
    catch(const char *error_str)
    {
        messaget message(get_message_handler());
        message.error().source_location=last_source_location;
        message.error() << error_str << messaget::eom;

        assert(0);
    }
    catch(std::bad_alloc)
    {
        error() << "Out of memory" << eom;
        assert(0);
    }

    statistics() << "size of program expression: "
                 << equation.SSA_steps.size()
                 << " steps" << eom;


    after=current_time();

    status() << "SYMEX TIME: " << (after-before) << eom;

    if(remaining_vccs!=0 || force_check)
    {
        if (use_slicing) {
          before=current_time();
            status() << "All SSA steps: " << equation.SSA_steps.size() << eom;
            symex_slicet symex_slice;
            symex_slice.slice(equation);
            status() << "Ignored SSA steps after slice: " << equation.count_ignored_SSA_steps() << eom;
            after=current_time();
            status() << "SLICER TIME: " << (after-before) << eom;
        }
    } else {
        status() << "Assertion(s) hold trivially(.)" << eom;
        return true;
    }
    return false;
}

