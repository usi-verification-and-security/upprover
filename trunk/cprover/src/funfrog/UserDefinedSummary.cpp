#include "UserDefinedSummary.h"

#include "solvers/smtcheck_opensmt2_lra.h"
#include "solvers/smtcheck_opensmt2_cuf.h"
#include "solvers/smtcheck_opensmt2_uf.h"
#include "symex_assertion_sum.h"
#include "smt_partitioning_target_equation.h"
#include "partition_iface.h"
#include "smt_summary_store.h"
#include "subst_scenario.h"
 

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
    unsigned int unwind,     
    std::string logic,    
    const std::string& summary_file)
{
    throw std::logic_error{"Not implemented after reactoring"};
    // Create the basic formula 
//    smt_summary_storet summary_store;
//    subst_scenariot omega {goto_functions, unwind};
//
//    // FIXME: remove pointer after SSA_Reportert class takes the code from
//    // partitioning_target_equationt into the reportert code
//    smt_partitioning_target_equationt* equation =
//            new smt_partitioning_target_equationt(ns, summary_store, true);
//
//    /* TODO:
//    symex_assertion_sumt symex = symex_assertion_sumt(
//            summarization_context, summary_info, ns, symbol_table,
//            equation, message_handler, goto_program, last_assertion_loc,
//            single_assertion_check, !no_slicing_option, !no_ce_option, true, unwind_bound,
//            options.get_bool_option("partial-loops"));
//
//    symex.prepare_SSA(assertion);
//     *
//     */
//
//    // Created decider - basic only
//    if(logic == "qfuf")
//        decider = new smtcheck_opensmt2t_uf("uf checker");
//
//    else if(logic == "qfcuf")
//        decider = new smtcheck_opensmt2t_cuf(8, 0, "cuf checker");
//
//    else //if(logic == "qflra")
//        decider = new smtcheck_opensmt2t_lra(0, "lra checker");
//
//    std::vector<summaryt*> templates;
//    smtcheck_opensmt2t* decider_smt = dynamic_cast <smtcheck_opensmt2t*> (decider);
//    equation->fill_function_templates(*decider_smt, templates);
//    decider_smt = nullptr;
//    for(unsigned int i = 0; i < templates.size(); ++i) {
//        smt_summaryt * smt_summary = dynamic_cast<smt_summaryt*>(templates[i]);
//        if(smt_summary){
//            summary_store.insert_summary(smt_summary,smt_summary->getTterm());
//
//        }
//    }
//    // Store the summaries
//    if (!summary_file.empty()) {
//        ofstream out{summary_file};
//        summary_store.serialize(out);
//    }
}
