/* 
 For testing only
 * Gets file name of facts in SMT-Lib or Coq 
 */

#include "facts.h"
#include "facts_smt.h"
#include "facts_summary_builder.h"
#include <iostream>

// Call: ./smtbuild input_file_example__mod_facts_smt.txt __summaries_mod_lra
// 1: input with all the facts
// 2: output **new** summary files
int main(int argc, const char **argv)
{
    if (argc < 3) {
        std::cerr << "Missing file facts name as input and/or output summary file name." << std::endl;
        return 1;
    }
    
    facts_smtt* facts = new facts_smtt();
    if (!facts->load_facts(argv[1])) {
        std::cerr << "Error reading the input file: " << argv[1] << std::endl;
        return 1;   
    }
    
    facts_summary_buildert* summary_writer = new facts_summary_buildert(*facts);
    
    std::set<std::string> empty; // empty for lra
    summary_writer->write_summary_facts(argv[2], empty);
    
    free(facts);
    free(summary_writer);
    
    return 0;
}
