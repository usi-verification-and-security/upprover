/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */

/* 
 * File:   symex_assertion_no_partition.h
 * Author: karinek
 *
 * Created on 20 April 2017, 17:51
 */

#ifndef SYMEX_ASSERTION_NO_PARTITIONT_H
#define SYMEX_ASSERTION_NO_PARTITIONT_H

#include <goto-programs/goto_program.h>
#include <goto-programs/goto_functions.h>
#include <goto-symex/goto_symex.h>
#include <goto-symex/goto_symex_state.h>
#include <cbmc/symex_bmc.h>
#include <namespace.h>
#include <symbol.h>
#include <ui_message.h>
#include <util/options.h>
#include <util/time_stopping.h>

#include "../assertion_info.h"
#include "smt_symex_target_equation.h"

class symex_no_partitiont : public symex_bmct {
public:
    symex_no_partitiont(
          const namespacet &_ns,
          symbol_tablet &_new_symbol_table,
          smt_symex_target_equationt &_target,
          ui_message_handlert &_message_handler,
          const goto_programt &_goto_program,
          unsigned _last_assertion_loc,  
          bool _single_assertion_check,
          bool _use_slicing=true,
	  bool _do_guard_expl=true,
          bool _use_smt=true
          ) :
          symex_bmct(_ns, _new_symbol_table, _target),
          equation(_target),
          current_assertion(NULL),
          message_handler(_message_handler),
          goto_program(_goto_program),
          last_assertion_loc(_last_assertion_loc),
          loc(0),
          single_assertion_check(_single_assertion_check),
          use_slicing(_use_slicing),
	  do_guard_expl(_do_guard_expl),
          use_smt(_use_smt)
          {set_message_handler(_message_handler);}
    
    virtual ~symex_no_partitiont() {} // Here there are no partition to delete
    
// Methods:    
    bool prepare_SSA(const assertion_infot &assertion, const goto_functionst& goto_functions);
    
    bool refine_SSA(const assertion_infot &assertion, bool force_check);


// Data Members    
    std::map<irep_idt, std::string> guard_expln;
    
private:
    // Store for the symex result
    smt_symex_target_equationt &equation;
    
    const goto_programt &goto_program;

    // Current assertion
    const assertion_infot* current_assertion;
    
    // Symex state holding the renaming levels
    goto_symext::statet state;
  
    ui_message_handlert &message_handler;    
    
    unsigned last_assertion_loc;

    unsigned loc;
    
    bool single_assertion_check;

    bool use_slicing;

    bool do_guard_expl;
  
    bool use_smt; // for slicing  
    
    bool process_planned(statet &state, const goto_functionst &goto_functions, bool force_check);

};

#endif /* SYMEX_ASSERTION_NO_PARTITIONT_H */

