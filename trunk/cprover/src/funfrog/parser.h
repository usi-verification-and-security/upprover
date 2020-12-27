#ifndef ABSTRACT_PARSER_H
#define ABSTRACT_PARSER_H

#include <fstream>
#include <iostream>
#include <util/string2int.h>
#include "xml_interface.h"
#include "util/parse_options.h"
#include "funfrog/utils/time_utils.h"
#include <goto-programs/adjust_float_expressions.h>
#include <goto-programs/remove_function_pointers.h>
//#include <goto-programs/goto_convert_functions.h>
//#include <goto-programs/remove_returns.h> // KE: never include this header

#include <goto-programs/remove_vector.h>
#include <goto-programs/remove_complex.h>

#include <goto-programs/set_properties.h>

#include <goto-programs/string_abstraction.h>
#include <goto-programs/string_instrumentation.h>

#include <goto-programs/rewrite_union.h>

#include <pointer-analysis/add_failed_symbols.h>

#include <analyses/goto_check.h>
#include <ansi-c/cprover_library.h>
#include <cpp/cprover_library.h>
#include <goto-programs/link_to_library.h> // Only for prop logic!
#include <goto-programs/mm_io.h>
#include <goto-programs/goto_inline.h>
#include <goto-programs/remove_virtual_functions.h>
#include <goto-programs/remove_skip.h>
#include <goto-programs/goto_functions.h>
#include <goto-programs/initialize_goto_model.h>
#include <goto-programs/read_goto_binary.h>
#include <goto-programs/instrument_preconditions.h>
#include <goto-programs/show_symbol_table.h>
#include <goto-programs/show_goto_functions.h>
#include <goto-programs/show_properties.h>
#include "UserDefinedSummary.h" // TODO: doesn't work yet, only contains original code
#include <funfrog/utils/naming_helpers.h>
#include <goto-instrument/unwind.h>
#include <goto-instrument/nondet_static.h>
#include <ansi-c/c_object_factory_parameters.h>

#include "check_claims.h"
//since Cprover5.12
#include <util/exit_codes.h>
#include <ansi-c/gcc_version.h>
#include <ansi-c/c_preprocess.h>
#include <langapi/language.h>
#include <langapi/mode.h>
#include <goto-checker/multi_path_symex_checker.h>
#include <goto-checker/multi_path_symex_only_checker.h>
#include <goto-checker/properties.h>
#include <goto-checker/single_loop_incremental_symex_checker.h>
#include <goto-checker/single_path_symex_checker.h>
#include <goto-checker/single_path_symex_only_checker.h>
#include <goto-checker/stop_on_fail_verifier.h>
#include <goto-checker/stop_on_fail_verifier_with_fault_localization.h>
#include <goto-checker/all_properties_verifier_with_trace_storage.h>
#include <goto-checker/all_properties_verifier_with_fault_localization.h>
#include <goto-checker/all_properties_verifier.h>
#include <goto-checker/cover_goals_verifier_with_trace_storage.h>



class parser_baset : public parse_options_baset, public xml_interfacet, public messaget
    {
public:
    parser_baset(const std::string &_optstring, const std::string &program, int argc, const char **argv ):
            parse_options_baset(_optstring, argc, argv, program),
            xml_interfacet(cmdline),
            messaget(ui_message_handler),
            ui_message_handler(cmdline, program)
    {
    }

protected:
    bool validate_input_options ();
    
    //goto_modelt goto_model;   //removed due to the need of having several goto-models in upprover
    
    ui_message_handlert ui_message_handler; // KE: due to change from register_languages to messaget
    
    unsigned claim_user_nr = 0;
    claim_numberst claim_numbers;
    claim_checkmapt claim_checkmap;
    
    void set_default_options(optionst &);
    
    void register_languages();
    void get_command_line_options(optionst &);
    void preprocessing(const optionst &);
    bool set_properties(goto_modelt &);
    
    unsigned count(const goto_functionst &goto_functions) const;
    unsigned count(const goto_programt &goto_program) const;

//move it outside of this class to be a standalone function for processing several goto-model in a single run
//bool process_goto_program(const optionst &);
    int get_goto_program(goto_modelt &,
                          const optionst &,
                          const cmdlinet &,
                          ui_message_handlert &);
    
    void calculate_show_claims(goto_modelt &);
    void set_options(const cmdlinet &cmdline);
    
    optionst options;
    std::ofstream statfile;
};

//Declaration:
// A standalone function; originally it was a member function of above class
bool process_goto_program(const cmdlinet &cmdline, const optionst &, goto_modelt &goto_model,
                          messaget &message);


#endif //ABSTRACT_PARSER_H
