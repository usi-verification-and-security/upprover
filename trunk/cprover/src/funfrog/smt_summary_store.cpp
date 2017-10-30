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
    for (storet::const_iterator it = store.begin();
         it != store.end();
         ++it) {
        if (it->is_repr()) {
            it->summary->serialize(out);
        }
    }
}

// In case we re-create the solver, we need to refresh the tterms in OpenSMT
void smt_summary_storet::refresh_summaries_tterms(const std::string &in, smtcheck_opensmt2t *decider) {
    // KE: add support for many summary files for lattice refinement
    std::set<std::string> summary_files;
    get_files(summary_files, in);
    for (auto it = summary_files.begin(); it != summary_files.end(); ++it) {
        if (decider->getMainSolver()->readFormulaFromFile(it->c_str())) {
            vec<Tterm> &functions = decider->getLogic()->getFunctions();
            storet::iterator itr = store.begin();
            for (int i = 0; i < functions.size(); ++i) {
                Tterm &tterm = functions[i];

                // Get the old summary and update it
                itr->summary->setTterm(tterm);
                itr->summary->setLogic(decider->getLogic());
                itr->summary->setInterpolant(tterm.getBody());

                // set for the next iteration
                itr++;
            }
        }
    }
}

// SMT logics deser
void smt_summary_storet::deserialize(const std::string &in, smtcheck_opensmt2t *decider) {
    repr_count = 0;

    if (!decider)
        return;

    store.clear();

    // KE: add support for many summary files for lattice refinement
    std::set<std::string> summary_files;
    get_files(summary_files, in);
    for (auto it = summary_files.begin(); it != summary_files.end(); ++it) {
        if (decider->getMainSolver()->readFormulaFromFile(it->c_str())) {
            vec<Tterm> &functions = decider->getLogic()->getFunctions();
            for (int i = 0; i < functions.size(); ++i) {
                summaryt *itp = new smt_summaryt();
                Tterm &tterm = functions[i];
                std::string fname = tterm.getName();
                clean_name(fname);
                int midx = get_max_id(fname);
                int next_idx = midx + 1;
                ++max_ids[fname];
                std::string summaryName = quote(add_counter(fname, next_idx));
                tterm.setName(summaryName);
                itp->setTterm(tterm);
                itp->setLogic(decider->getLogic());
                itp->setInterpolant(tterm.getBody());
                itp->set_valid(true);
                store.push_back(nodet(i, *itp));
                repr_count++;
            }

            max_id += repr_count; // KE: We add new summaries so we need to inc the max
        }
    }

    return;
}

/*******************************************************************\

Function: summary_storet::insert_summary

  Inputs:

 Outputs:

 Purpose: Inserts a new summary, the given summary is invalidated

\*******************************************************************/

summary_idt smt_summary_storet::insert_summary(summaryt &summary) {
    summary_idt id = max_id++;
    summary.set_valid(true);

    // Here gets the function names
    Tterm *tterm = summary.getTterm();
    assert(tterm);
    string fname = tterm->getName();
    // at this point, there should be just the name of the original function
    assert(!is_quoted(fname));
    assert(!contains_counter(fname));
    int midx = get_max_id(fname);
    int next_idx = midx + 1;
    max_ids[fname] = next_idx;// = max(fidx, midx);
    // as name of the summary, store the quoted version with counter from the store
    std::string fixed_name = quote(add_counter(fname, next_idx));
    tterm->setName(fixed_name);

    store.push_back(nodet(id, summary));
    repr_count++;
    return id;
}

/*
 Returns a list of summary files
 */
void get_files(std::set<std::string> &files, std::string set) {

    int length = set.length();

    for (int idx = 0; idx < length; idx++) {
        std::string::size_type next = set.find(",", idx);
        files.insert(set.substr(idx, next - idx));

        if (next == std::string::npos) break;
        idx = next;
    }
}