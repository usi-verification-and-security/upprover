#include "read_fact_files.h"
#include <iostream>

// Call: ./extractsum <declaration file name> <facts file name> <output smt file base name> <flag_all_subsets>
// E.g., ./extractsum facts_decl.txt Coq_translate.txt build_output/smt_ false
// 1: input with all the facts
// 2: output subsets of the facts for the build of the lattice (true flag)
//    output an smt file with all the facts as query (false flag)
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
    bool is_all_subset = (string(argv[4]).compare("true") == 0);
    if (is_all_subset)
        facts_subsets_writer->save_facts_smt_queries(argv[3]);
    else 
    {
        if (argc > 5) {
            facts_subsets_writer->load_facts_names_only(argv[5]);
            facts_subsets_writer->save_subset_facts_smt_query(argv[3]);
        } else {
            facts_subsets_writer->save_facts_smt_query(argv[3]);
        }
    }
    free(facts_subsets_writer);
    // End of .smt files query creation for co-exist test


    // TODO: add missing extraction of query once needed


    return 0;
}
