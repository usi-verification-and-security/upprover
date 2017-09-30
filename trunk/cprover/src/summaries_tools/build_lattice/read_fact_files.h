/* 
 * File:   read_fact_files.h
 * Author: karinek
 *
 * Created on 22 September 2017, 17:16
 */

#ifndef READ_FACT_FILES_H
#define READ_FACT_FILES_H

#include <iostream>
#include <list>
#include <map>
#include <vector>
#include <set>

#include <algorithm>

using namespace std;

class read_fact_filest {
public:
    read_fact_filest() :file_no(0) {}
    virtual ~read_fact_filest() {}
    
    bool load_facts(string facts_query_base_file_name, string facts_decl_file_name, string facts_file_name); // All Stages
    bool load_facts_names_only(string facts_file_name); // Stage 3
    bool load_subset_facts_names(string facts_file_name); // Stage 4
    void save_facts_smt_queries(string facts_query_base_file_name); // Stage 2
    void save_facts_smt_query(string facts_query_base_file_name); // Stage 2
    void save_subset_facts_smt_query(string facts_query_base_file_name); // Stage 3
    void save_implies_pair_facts_smt_query(string facts_query_base_file_name); //Stage 4
    void save_implies_3_facts_smt_query(string facts_query_base_file_name); //Stage 4
    
private:
    std::list<std::string> facts_subset; // Stage 3
    std::list<std::string> facts_subsets; // Stage 4
    std::list<std::string> decls; // All stages
    std::map<std::string,std::string> facts; // All Stages
    int file_no; // When writting to avoid duplicate names
    
    string original_header_function;
    string original_function_name;
    string original_params_function;
    
    string create_local_call_to_orig_func(string fact_name);
    string create_params_args_connection(string fact_name);
    string create_string_of_single_fact(string fact_name, string fact);
    bool is_same_set(string fact1, string fact2);

    vector<vector<pair<string,string>>> create_all_subsets_of_facts(vector<pair<string,string>> set_facts);
    void write_smt_query(string facts_str, string decls_str, string base_name, string start_fact_name, string counter);
    void write_pairs_impl_query(string facts_query_base_file_name, 
            string smt_decl, pair<string,string> pos, pair<string,string> neg);

    void split(std::list<std::string>& strings, std::string list, std::string split_str);
};

#endif /* READ_FACT_FILES_H */

