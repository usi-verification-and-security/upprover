#include "read_fact_files.h"
#include <iostream>

// Call: ./extractsum <declaration file name> <facts file name> <output smt file base name> <flag_all_subsets>
// E.g., ./extractsum facts_decl.txt Coq_translate_wt_implies.txt build_output/smt_impl_ __smt_all_facts_name_subset.txt
// 1: input with all the facts
// 2: output pairs to test a==>b true
int main(int argc, const char **argv)
{
    if (argc < 5) {
        std::cerr << "Missing file facts name or/and declaration facts name and/or output smt file name." << std::endl;
        return 1;
    }

    // ouputs smt files with subsets of facts from the input file
    read_fact_filest* facts_subsets_writer = new read_fact_filest();
    if (!facts_subsets_writer->load_facts(argv[3], argv[1], argv[2])) {
        std::cerr << "Error reading the input file: " << argv[1] << " and/or " << argv[2] << std::endl;
        return 1;
    }
    
    facts_subsets_writer->load_subset_facts_names(argv[4]);
    facts_subsets_writer->save_implies_pair_facts_smt_query(argv[3]);
    facts_subsets_writer->save_implies_3_facts_smt_query(argv[3]);
    facts_subsets_writer->save_implies_4_facts_smt_query(argv[3]);
    // add also a&b => c check

    free(facts_subsets_writer);
    // End of .smt files query creation for co-exist test


    // TODO: add missing extraction of query once needed


    return 0;
}
