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
//#include <algorithm>

using namespace std;

class read_fact_filest {
public:
    read_fact_filest() :file_no(0) {}
    virtual ~read_fact_filest() {}
    
    bool load_facts(string facts_decl_file_name, string facts_file_name);
    void save_facts_smt_queries(string facts_query_base_file_name);
    
private:
    std::set<std::string> decls;
    std::map<std::string,std::string> facts;
    int file_no; // When writting to avoid duplicate names
    
    string original_header_function;
    string original_function_name;
    
    string create_local_call_to_orig_func(string fact_name);
    string create_params_args_connection(string fact_name);
    string create_string_of_single_fact(string fact_name, string fact);

    vector<vector<pair<string,string>>> create_all_subsets_of_facts(vector<pair<string,string>> set_facts);
    void write_smt_query(string facts_str, string decls_str, string base_name, string start_fact_name, string counter);

    void split(std::list<std::string>& strings, std::string list, std::string split_str);
};

#endif /* READ_FACT_FILES_H */

