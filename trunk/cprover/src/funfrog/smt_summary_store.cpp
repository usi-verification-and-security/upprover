/*******************************************************************\

Module: Storage class for function summaries (union-find).

\*******************************************************************/

#include "solvers/smt_itp.h"
#include "smt_summary_store.h"
#include "solvers/smtcheck_opensmt2.h"

#include "utils/naming_helpers.h"

// Serialization in SMT //print summary
void smt_summary_storet::serialize(std::ostream &out) const {
    decider->getLogic()->dumpHeaderToFile(out);
    for (const auto & summary_node : store){
    //assert(summary_node.is_repr();
            summary_node.summary->serialize(out);
    }
}


// SMT logics deser
void smt_summary_storet::deserialize(std::vector<std::string> fileNames) {

    if (!decider){
        std::cerr << "Could not deresialize summary store, the solver handle was not set!\n";
        return;
    }
    this->clear();

    size_t old_function_count = 0;
    for (const auto & fileName : fileNames) {
        try {
            if (decider->read_formula_from_file(fileName)) {
                // std::cout << "\n----Read summary file: " << fileName << std::endl;
                auto & functions = decider->get_functions();
                assert(old_function_count <= functions.size());
                // MB: function in OpenSMT are added when a file is read, so we can safely skip the ones
                // we have added previously; Also note that this will work only if functions in files have different names!
                for (size_t i = old_function_count; i < functions.size(); ++i) {
                    auto itp = new smt_itpt_summaryt();
                    // only copy assignment work correctly, copy constructor do not at the moment
                    itp->getTempl() = functions[i];
                    SummaryTemplate & summaryTemplate = itp->getTempl();
                    std::string fname = summaryTemplate.getName();
                    clean_name(fname);
                    summaryTemplate.setName(fname);
                    itp->setDecider(decider);
                    itp->setInterpolant(summaryTemplate.getBody());
                    this->insert_summary(itp, fname);
                }
                old_function_count = functions.size();
            }
        } catch (LANonLinearException & e){
            // OpenSMT with linear real arithmetic was trying to read a file with nonlinear operation in it
            // Ignore this file.
            std::cerr << "Non linear operation encounter in file " << fileName << ". Ignoring this file.\n";
        }
    }
}

/*******************************************************************\
 derived class of summary_storet
 Purpose: Inserts a new summary, summary store takes ownership of the pointer (itpt_summaryt*)
            summary_given --> ID
 NOTE: Due to UpProver's usage, this method inserts countered version of fname
\*******************************************************************/
summary_idt smt_summary_storet::insert_summary(itpt_summaryt *summary_given, const std::string & function_name) {
    smt_itpt_summaryt * smt_summary = dynamic_cast<smt_itpt_summaryt*>(summary_given);
    if(!smt_summary){
        std::string msg = "Error during an insertion of a summary into the summary store, not compatible type!\n";
        throw std::logic_error(msg);
    }
    // Here gets the function names
    SummaryTemplate & sumTemplate = smt_summary->getTempl();
    // at this point, there should be just the name of the original function
    assert(!is_quoted(function_name));
    assert(!fun_name_contains_counter(function_name));
//    std::size_t next_idx = get_next_id(function_name);
    // as name of the summary, store the quoted version with counter from the store
//    const std::string fname_countered = quote(add_counter_to_fun_name(function_name, next_idx)); //|f#1|
    sumTemplate.setName(function_name);
    
    // call the base functionality
    //Due to one-to-one mapping of fname and its ID, lets store fname with countered versions
    return summary_storet::insert_summary(summary_given, function_name);
}