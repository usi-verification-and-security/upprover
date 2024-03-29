/******************************************************************
 * File:   symex_assertion_no_partitiont.cpp
 * Author: karinek
 * Created on 20 April 2017
*******************************************************************/
#include "symex_no_partition.h"
#include "../utils/time_utils.h"

#include <util/expr_util.h>
#include <goto-symex/goto_symex_state.h>
#include <goto-symex/symex_slice_class.h>

#include "hifrog_symex_target_equation_no_partition.h"
#include "../assertion_info.h"

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
  reset_state(); //cprover5.12

  // Old: ??? state.value_set = value_sets;
  //prepare_fresh_arg_symbols(*state, partition_iface);
  statePtr->source.pc = goto_program.instructions.begin();
  
  loc = 0;
  return process_planned(*statePtr, goto_functions, false); // In it, in the end need to call convert
}



bool symex_no_partitiont::refine_SSA(const assertion_infot &assertion, bool force_check)
{
    // TODO
    return false;
}

bool symex_no_partitiont::process_planned(statet &state, const goto_functionst &goto_functions, bool force_check)
{
    // Proceed with symbolic execution
    auto before=timestamp();

    // Taken from bmc.cpp (main)
    try
    {
        // perform symbolic execution        
        //this->operator () (statePrt, goto_functions, goto_program);
        get_goto_functiont get_goto_function = construct_get_goto_function(goto_functions);
        this->symex_with_state(state, get_goto_function, new_symbol_table);

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
    catch(const std::bad_alloc &)
    {
        log.error() << "Out of memory" << log.eom;
        assert(0);
    }

    statistics() << "size of program expression: "
                 << equation.SSA_steps.size()
                 << " steps" << log.eom;


    auto after=timestamp();

    status() << "SYMEX TIME: " << time_gap(after,before) << log.eom;

    if(_remaining_vccs!=0 || force_check)
    {
        if (use_slicing) {
            before=timestamp();
            status() << "All SSA steps: " << equation.SSA_steps.size() << log.eom;
            symex_slicet symex_slice;
            symex_slice.slice(equation);
            status() << "Ignored SSA steps after slice: " << equation.count_ignored_SSA_steps() << log.eom;
            after=timestamp();
            status() << "SLICER TIME: " << time_gap(after,before) << log.eom;
        }
    } else {
        status() << "Assertion(s) hold trivially(.)" << log.eom;
        return true;
    }
    return false;
}

bool symex_no_partitiont::get_unwind(const symex_targett::sourcet & source, const statet::call_stackt &context, unsigned unwind) {
    // returns true if we should not continue unwinding
    // for support of different bounds in different loops, see how it's done in symex_bmct
    return unwind >= max_unwind;
}

symex_no_partitiont::symex_no_partitiont(const optionst & _options, path_storaget & _path_storage,
                                         const symbol_tablet & _outer_symbol_table,
                                         hifrog_symex_target_equationt & _target, message_handlert & _message_handler,
                                         const goto_programt & _goto_program, bool _use_slicing)
 :
    goto_symext(_message_handler, _outer_symbol_table, _target, _options, _path_storage),
            equation(_target),
            goto_program(_goto_program),
            current_assertion(nullptr),
            loc(0),
            use_slicing(_use_slicing)
    {}

