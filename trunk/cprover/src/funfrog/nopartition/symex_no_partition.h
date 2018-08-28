/* 
 * File:   symex_assertion_no_partition.h
 * Author: karinek
 *
 * Created on 20 April 2017, 17:51
 */

#ifndef SYMEX_ASSERTION_NO_PARTITIONT_H
#define SYMEX_ASSERTION_NO_PARTITIONT_H

#include <goto-symex/goto_symex.h>

class hifrog_symex_target_equationt;
class assertion_infot;

class symex_no_partitiont : public goto_symext {
public:
    symex_no_partitiont(
            const namespacet &_ns,
            symbol_tablet &_new_symbol_table,
            hifrog_symex_target_equationt &_target,
            message_handlert &_message_handler,
            const goto_programt &_goto_program,
            bool _use_slicing=true
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
    bool get_unwind(const symex_targett::sourcet & source, unsigned unwind) override;

private:
    unsigned int max_unwind = 1;
    // Store for the symex result
    hifrog_symex_target_equationt &equation;
    
    const goto_programt &goto_program;

    // Current assertion
    const assertion_infot* current_assertion;
    
    // Symex state holding the renaming levels
    goto_symext::statet state;

    unsigned loc;

    bool use_slicing;
    
    bool process_planned(statet &state, const goto_functionst &goto_functions, bool force_check);

};

#endif /* SYMEX_ASSERTION_NO_PARTITIONT_H */

