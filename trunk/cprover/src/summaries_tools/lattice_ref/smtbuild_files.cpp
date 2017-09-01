/* 
 * File:   smtbuild_filest.cpp
 * Author: karinek
 * 
 * Created on 12 May 2017, 10:39
 */

#include "smtbuild_files.h"

// Init for text files - shall have one file + parsing for smt files
void smtbuild_filest::init_smtbuild_data(std::string f_decls, std::string f_facts, std::string f_facts2i)
{
    /* Reads Declarations of SMT file */
    std::ifstream input(f_decls);
    if (!input.is_open()) 
    {
        std::cout << "Cannot find file f_decls: " << f_decls << std::endl;
        exit(0);
    }
    
    std::string line;
    while( std::getline( input, line ) ) {
        decls.insert(line);
    }
    
    /* Reads Facts from file - one fact per line */
    std::ifstream input_facts(f_facts);
    if (!input_facts.is_open()) 
    {
        std::cout << "Cannot find file f_facts: " << f_facts << std::endl;
        exit(0);
    }
    
    while( std::getline( input_facts, line ) ) {
        facts.insert(line);
    }

    /* Reads Facts from file - one fact per line */
    std::ifstream input_facts2i(f_facts2i);
    if (!input_facts2i.is_open()) 
    {
        std::cout << "Cannot find file f_facts2i: " << f_facts2i << std::endl;
        exit(0);
    }
    
    while( std::getline( input_facts2i, line ) ) {
        facts2impl.insert(line);
    }    
    
    
    std::cout << "Created data, declaration size: " << decls.size() 
            << ", facts size " << facts.size() << std::endl;
}

// Write a file and return how many files wrote in test_path
int smtbuild_filest::smtwrite_implication_tests(std::string test_path) 
{    
    std::string smt_decl = "";
    std::string basic = "(assert (and \n  (not (= 0 n)) \n  (= mod_hifrog_c_unsupported_op2var0_1 (modd a n)) \n  (= mod_hifrog_c_unsupported_op2var0_2 (modd b n))\n  ";
    std::string logic = "\n";
    //std::string basic = "(assert (and \n  (not (= 0 n)) \n  (= mod_hifrog_c_unsupported_op2var0_1 (mod a n)) \n  (= mod_hifrog_c_unsupported_op2var0_2 (mod b n))\n  ";
    //std::string logic = "(set-logic QF_LRA)\n";
    
    for ( auto it = decls.begin(); it != decls.end(); it++ )
        smt_decl += (*it) + " \n";
    
    
    // Creates files of !(!a or b) which is a and !b = unsat says b depends on b
    int file_no = 0;
    for ( auto it = facts.begin(); it != facts.end(); it++ ) {
        for ( auto it2 = facts2impl.begin(); it2 != facts2impl.end(); it2++ ) {
            // Create the whole implication statement
            if ((*it2).compare(*it) != 0) // If not the same fact
            {
                std::string temp = logic + smt_decl + basic + (*it) + "\n  (not " 
                        + (*it2) + "\n)))\n(check-sat)\n";

                // Write to a file: (test_path + file_no)
                ofstream smtfile;
                smtfile.open (test_path + std::to_string(file_no) + ".smt2");
                smtfile << temp;
                smtfile.close();

                // Inc the counter file_no
                file_no++;
            }
        }
    }
    
    return file_no;
}
