#include "UserDefinedSummary.h"

#include "solvers/smtcheck_opensmt2_lra.h"
#include "solvers/smtcheck_opensmt2_cuf.h"
#include "solvers/smtcheck_opensmt2_uf.h"
#include "symex_assertion_sum.h"
#include "partition_iface.h"
#include "smt_summary_store.h"
#include "subst_scenario.h"
#include "partitioning_target_equation.h"
#include "solvers/smt_itp.h"
#include "assertion_info.h"
 

/*******************************************************************\
  
 Function: UserDefinedSummaryt::dump_list_templates

 Inputs:

 Outputs:

 Purpose: LA original function list_templates moved to a new class

\*******************************************************************/
void UserDefinedSummaryt::dump_list_templates(
    namespacet &ns, 
    const goto_programt &goto_program, 
    const goto_functionst &goto_functions,
    const optionst & options,
    unsigned int unwind,     
    std::string logic,    
    const std::string& summary_file, ui_message_handlert & ui_message_handler)
{

    // Created decider - basic only
    solver_optionst so;
    if(logic == "qfuf")
        decider = new smtcheck_opensmt2t_uf(so, "uf checker");

    else if(logic == "qfcuf")
        decider = new smtcheck_opensmt2t_cuf(so, "cuf checker");

    else //if(logic == "qflra")
        decider = new smtcheck_opensmt2t_lra(so, "lra checker");

    smt_summary_storet summary_store(decider);
    subst_scenariot omega {goto_functions, unwind};
    // initialize the omega
    omega.initialize_call_info(omega.get_call_tree_root(), goto_program);
    omega.setup_default_precision(get_init_mode(options.get_option("init-mode")));
    // set all functions to inline, no summaries
    auto has_summary = [](const std::string & function_name){
        return false;
    };
    assertion_infot ass_info;
    omega.set_initial_precision(ass_info, has_summary);
    
    partitioning_target_equationt equation (ns, summary_store, true, ui_message_handler);

    std::unique_ptr<path_storaget> worklist;
    ui_message_handler.set_verbosity(messaget::M_STATISTICS);
    guard_managert guard_manager; //since CBMC5.12
    symex_assertion_sumt symex(
            goto_functions, omega.get_call_tree_root(), options, *worklist, ns.get_symbol_table(),
            equation, ui_message_handler, goto_program, INT_MAX,
            true, true, unwind,
            options.get_bool_option("partial-loops"), guard_manager);

    symex.set_assertion_info_to_verify(&ass_info);

    symex.prepare_SSA();

    std::vector<itpt_summaryt*> templates;
    equation.fill_function_templates(*decider, templates);
    for(unsigned int i = 0; i < templates.size(); ++i) {
        smt_itpt_summaryt * smt_summary = dynamic_cast<smt_itpt_summaryt*>(templates[i]);
        if(smt_summary){
            summary_store.insert_summary(smt_summary,smt_summary->getTempl().getName());

        }
    }
    // Store the summaries
    if (!summary_file.empty()) {
        ofstream out{summary_file};
        summary_store.serialize(out);
    }
}
