/*******************************************************************
 * File:   symex_assertion_no_partition.h
 * Author: karinek
 * Created on 20 April 2017
 *******************************************************************/

#ifndef SYMEX_ASSERTION_NO_PARTITIONT_H
#define SYMEX_ASSERTION_NO_PARTITIONT_H

#include <goto-symex/goto_symex.h>
class hifrog_symex_target_equationt;
class assertion_infot;
class path_storaget;

class symex_no_partitiont : public goto_symext {
public:
    symex_no_partitiont(
            const optionst & _options,
            path_storaget & _path_storage,
            const symbol_tablet & _outer_symbol_table,
            hifrog_symex_target_equationt & _target,
            message_handlert & _message_handler,
            const goto_programt & _goto_program,
            bool _use_slicing = true
    );
    
    virtual ~symex_no_partitiont() {} // Here there are no partition to delete

// Methods:    
    bool prepare_SSA(const assertion_infot &assertion, const goto_functionst& goto_functions);
    
    bool refine_SSA(const assertion_infot &assertion, bool force_check);

    messaget::mstreamt & status() {
        return log.status();
    }

    messaget::mstreamt & error() {
        return log.error();
    }

    messaget::mstreamt & statistics() {
        return log.statistics();
    }

    void setup_unwind(unsigned int max_unwind) { this->max_unwind = max_unwind; }

// Data Members    
    std::map<irep_idt, std::string> guard_expln;
protected:
    bool get_unwind(
    const symex_targett::sourcet &source,
    const statet::call_stackt &context,
    unsigned unwind);

private:
    // to be able to start with a fresh statePrt
    void reset_state(){
//      auto* storage = &this->path_storage;
//      assert(storage);
      // Clear the state
      statePtr.reset(new goto_symext::statet());
//          symex_targett::sourcet(goto_functionst::entry_point(), goto_program),
//          [storage](const irep_idt &id) { return storage->get_unique_l2_index(id); }));
      ns = namespacet{outer_symbol_table, statePtr->symbol_table};

      // since not supporting multiple threads, we do not need to record events;
      turn_off_recording_events();
    }

    void turn_off_recording_events() {
      // turns off doing some book-keeping related to handling multiple threads by CProver
      statePtr->record_events = false;
    }
    
    unsigned int max_unwind = 1;
    // Store for the symex result
    hifrog_symex_target_equationt &equation;
    
    const goto_programt &goto_program;
    //const goto_functionst& goto_functions;

    // Current assertion
    const assertion_infot* current_assertion;
    
    // Symex statePrt holding the renaming levels
    std::unique_ptr<statet> statePtr; //HiFrog specific

    unsigned loc;

    bool use_slicing;
    
    symbol_tablet new_symbol_table;
    
    bool process_planned(statet &state, const goto_functionst &goto_functions, bool force_check);

};

#endif /* SYMEX_ASSERTION_NO_PARTITIONT_H */

