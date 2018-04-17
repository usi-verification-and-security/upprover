/*******************************************************************\

Module: Storage class for function summaries (union-find).

Author: Ondrej Sery

\*******************************************************************/

#include "solvers/smt_itp.h"
#include "smt_summary_store.h"
#include "solvers/smtcheck_opensmt2.h"

#include "utils/naming_helpers.h"

// Serialization SMT
void smt_summary_storet::serialize(std::ostream &out) const {
    for (auto it = store.begin();
         it != store.end();
         ++it) {
        if (it->is_repr()) {
            it->summary->serialize(out);
        }
    }
}

// SMT logics deser
void smt_summary_storet::deserialize(std::vector<std::string> fileNames) {

    if (!decider){
        std::cerr << "Could not deresialize summary store, the solver handle was not set!\n";
        return;
    }
    repr_count = 0;
    store.clear();

    for (const auto & fileName : fileNames) {
        if (decider->getMainSolver()->readFormulaFromFile(fileName.c_str())) {
            vec<Tterm> &functions = decider->getLogic()->getFunctions();
            for (int i = 0; i < functions.size(); ++i) {
                auto itp = new smt_summaryt();
                Tterm &tterm = functions[i];
                std::string fname = tterm.getName();
                clean_name(fname);
                auto next_idx = get_next_id(fname);
                std::string summaryName = quote(add_counter_to_fun_name(fname, next_idx));
                tterm.setName(summaryName);
                itp->setTterm(tterm);
                itp->setLogic(decider->getLogic());
                itp->setInterpolant(tterm.getBody());
                itp->set_valid(true);
                // FIXME: when reading multiple files, this would assign the same ID to multiple summaries
                store.emplace_back(i, itp);
                repr_count++;
            }

            max_id += repr_count; // KE: We add new summaries so we need to inc the max
        }
    }
    //FIXME: update also map from function names to summary_ids
}

/*******************************************************************\

Function: summary_storet::insert_summary

  Inputs:

 Outputs:

 Purpose: Inserts a new summary, the given summary is invalidated

\*******************************************************************/

void smt_summary_storet::insert_summary(summaryt *summary, const irep_idt &function_name) {
    smt_summaryt * smt_summary = dynamic_cast<smt_summaryt*>(summary);
    if(!smt_summary){
        std::cerr << "Ignoring insertion of a summary into the summary store, not compatible type\n";
        return;
    }
    summary_idt id = max_id++;

    // Here gets the function names
    Tterm *tterm = smt_summary->getTterm();
    assert(tterm);
    string fname = tterm->getName();
    // at this point, there should be just the name of the original function
    assert(!is_quoted(fname));
    assert(!fun_name_contains_counter(fname));
    std::size_t next_idx = get_next_id(fname);
    // as name of the summary, store the quoted version with counter from the store
    std::string fixed_name = quote(add_counter_to_fun_name(fname, next_idx));
    tterm->setName(fixed_name);
    smt_summary->set_valid(true);
    store.emplace_back(id, smt_summary);
    function_to_summaries[function_name].push_back(id);
    repr_count++;
}
