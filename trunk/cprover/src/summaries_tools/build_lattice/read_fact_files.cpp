/* 
 * File:   read_fact_files.cpp
 * Author: karinek
 * 
 * Created on 22 September 2017, 17:16
 */

#include "read_fact_files.h"

#include <iostream>
#include <fstream>
using namespace std;

#include "../../funfrog/hifrog.h"

/*******************************************************************

 Function: read_fact_filest::load_facts

 Inputs: file name where all the declarations of the vars of the facts 
         are, and another file with all the facts
  
 Outputs: 

 Purpose: Good for the build of sub-sets of facts as .smt file for
          both stages, guard && fact and guard => facts.
 
\*******************************************************************/
bool read_fact_filest::load_facts(string facts_decl_file_name, string facts_file_name) 
{
    /* Reads Declarations of SMT file */
    std::ifstream input_decl(facts_decl_file_name);
    if (!input_decl.is_open())
    {
        std::cout << "Cannot find the facts's declarations file: " << facts_decl_file_name << std::endl;
        return false;
    }
    
    std::string line;
    while(std::getline(input_decl, line))
    {
        decls.insert(line);
    }
    
    /* Reads the facts */
    std::ifstream input_facts(facts_file_name);
    if (!input_facts.is_open())
    {
        std::cout << "Cannot open the facts' file: " <<  facts_file_name << std::endl;
        return false;
    }
    
    // Name of the original function. E.g., mod
    if (!std::getline(input_facts, line)) {
        std::cout << "Error reading original_function_name \n";
        return false;
    }
    original_function_name = line;
    std::cout << "Start loading " << facts_file_name << " function's facts: " << original_function_name << std::endl;
    
    // Declare of the original function
    if (!std::getline(input_facts, line)) {
        std::cout << "Error reading declare_original_function \n";
        return false;
    }
    // Skip it, we don't need if for this task
    
    // Define part of the original function header
    if (!std::getline(input_facts, line)) {
        std::cout << "Error reading original_header_function \n";
        return false;
    }
    original_header_function = line;
    
    // Define part of the original function header
    if (!std::getline(input_facts, line)) {
        std::cout << "Error reading is_return_unsigned \n";
        return false;
    }
    // Skip it, we don't need if for this task
    
    // in/out parameters of the facts
    if (!std::getline(input_facts, line)) {
        std::cout << "Error reading params_set_of_function \n";
        return false;
    }
    original_params_function = line;
    // Skip it, we don't need if for this task
    
    // Load the rest of the facts
    std::string name="";
    std::string fact="";
    std::cout << "==> Reading facts: ";
    while (std::getline(input_facts, name)) {
        if (name[0] == ';') continue;
        
        std::cout << name << " ";
        if (!std::getline(input_facts, fact)) {
            return false;
        }

        // Add name,fact
        facts.insert(pair<string, string> (name, fact));
    }
    std::cout << std::endl;
    
    std::cout << "** Added: " << facts.size() << " facts **" << std::endl;

    // Complete only if load facts
    return (facts.size() > 0);
}

/*******************************************************************

 Function: read_fact_filest::save_facts_smt_query

 Inputs: facts
  
 Outputs: facts in smt-lib query

 Purpose:
 
\*******************************************************************/
void read_fact_filest::save_facts_smt_query(string facts_query_base_file_name)
{
    // Create the declarations to the query (once to all queries)
    std::string smt_decl = "";
    for ( auto it = decls.begin(); it != decls.end(); it++ )
        smt_decl += (*it) + " \n";
    std::cout << "** Loading Declarations **" << std::endl;

    // Add all the subsets of facts to the file differnt files
    string query = "";
    for (auto i = facts.begin(); i != facts.end(); ++i)
    {
        string outter_fact = create_string_of_single_fact(i->first, i->second);
        query += "    ;; " + i->first +"\n";
        query += "    " + outter_fact + "\n";
    }
    
    std::cout << "** Building the Query **" << std::endl;
    
    // If not an empty set
    if (facts.size() > 0)
    {
        string fact_name = "all";
        string counter = "00";

        string params = original_params_function;
        string func_name = original_function_name;
        string return_val = "|" + func_name + FUNC_RETURN + "|" ;
        string orig_func_call = "(= (|_" + func_name + "#0| " + params + ") " + return_val + ")";
        
        query = "  (and \n    " + orig_func_call + "\n" + query + "  )\n";
        query = "(assert \n" + query + ")\n(check-sat)\n";

        std::cout << "** Saving the Query **" << std::endl;
        
        // write fact with only one fact:
        write_smt_query(query, smt_decl, facts_query_base_file_name, fact_name, counter);
        std::cout << "Writing Query " << fact_name << "::" << counter << " to file." << std::endl;
    }
}

/*******************************************************************

 Function: read_fact_filest::save_facts_smt_queries

 Inputs: facts
  
 Outputs: sub-set of facts in smt-lib query

 Purpose: main output of the smt queries for building the lattice
 ==> Input for the co-exist check
 
\*******************************************************************/
void read_fact_filest::save_facts_smt_queries(string facts_query_base_file_name)
{
    // Create the declarations to the query (once to all queries)
    std::string smt_decl = "";
    for ( auto it = decls.begin(); it != decls.end(); it++ )
        smt_decl += (*it) + " \n";
    std::cout << "** Loading Declarations **" << std::endl;
    
    // Create all the subsets of the current set of facts
    vector<pair<string,string>> set_facts;
    for (auto i = facts.begin(); i != facts.end(); ++i)
    	set_facts.push_back(pair<string, string> (i->first, i->second));
    std::cout << "** Creating a vector of facts **" << std::endl;

    vector< vector<pair<string,string>> > subsets = create_all_subsets_of_facts(set_facts);
    std::cout << "** Creating all subsets of the facts **" << std::endl;

    // Add all the subsets of facts to the file differnt files
    for (auto i = subsets.begin(); i != subsets.end(); ++i)
    {
    	// Build a query to a single subset of facts
    	string query = "";
    	for (auto j = i->begin(); j != i->end(); ++j)
    	{
    		string outter_fact = create_string_of_single_fact(j->first, j->second);
    		query += outter_fact + "\n";
    	}

    	// If not an empty set
    	if (i->size() > 0)
    	{
    		string fact_name = i->begin()->first;
    		string counter = std::to_string(i->size());

    		if (i->size() > 1)
    		{
    			query = "(and " + query + ")\n";
    		}
    		query = "(assert \n" + query + "\n)\n(check-sat)\n";

    		// write fact with only one fact:
    		write_smt_query(query, smt_decl, facts_query_base_file_name, fact_name, counter);
    		std::cout << "Writing Query " << fact_name << "::" << counter << " to file." << std::endl;
    	}
    }
}

/*******************************************************************

 Function: read_fact_filest::create_all_subsets_of_facts

 Inputs: facts

 Outputs: sub-set of facts in vectors

 Purpose:

\*******************************************************************/
vector< vector<pair<string,string>> > read_fact_filest::create_all_subsets_of_facts(vector<pair<string,string>> set_facts)
{
    vector< vector<pair<string,string>> > subset;
    vector<pair<string,string>> empty;
    subset.push_back( empty );

    for (unsigned i = 0; i < set_facts.size(); i++)
    {
        vector<vector<pair<string,string>>> subsetTemp = subset;

        for (unsigned j = 0; j < subsetTemp.size(); j++)
            subsetTemp[j].push_back(set_facts[i]);

        for (unsigned j = 0; j < subsetTemp.size(); j++)
            subset.push_back(subsetTemp[j]);
    }
    return subset;
}

/*******************************************************************

 Function: read_fact_filest::create_string_of_single_fact

 Inputs: a fact and its name

 Outputs: the fact as a string connected to the main arguments

 Purpose:

\*******************************************************************/
string read_fact_filest::create_string_of_single_fact(string fact_name, string fact)
{
    // definition of the original function - connect to inner fact
    string orig_func_call = create_local_call_to_orig_func(fact_name);
    // Created: (= (|_mod#0| |mod_Cd::a!0| |mod_Cd::n!0|) mod_Cd::return_value!0)

    string orig_params_connection = create_params_args_connection(fact_name);
    // Created: (and (= |_mod#0::a!0| |mod_Cd::a!0|) (= |_mod#0::n!0| |mod_Cd::n!0|))

    string outter_fact = "(and " + fact + " (and " + orig_func_call + " " + orig_params_connection + "))";

    return outter_fact;
}

/*******************************************************************

 Function: read_fact_filest::create_local_call_to_orig_func

 Inputs: fact name
  
 Outputs: the term that connects the fact to the original function  

 Purpose: 
 
\*******************************************************************/
string read_fact_filest::create_local_call_to_orig_func(string fact_name) {
    // definition of the original function - connect to inner fact
    string return_val = "|" + fact_name + FUNC_RETURN + "|" ;
    std::string params = original_params_function;
    std::string func_name = original_function_name;
    unsigned index = 0;
    while (params.find(func_name, index) != std::string::npos) {
        index = params.find(func_name, index);
        params = params.replace(index, func_name.size(),fact_name);
        index += fact_name.size();
    }
    string orig_func_call = "(= (|_" + func_name + "#0| " + params + ") " + return_val + ")";
    // Created: (= (|_mod#0| |mod_Cd::a!0| |mod_Cd::n!0|) mod_Cd::return_value!0)

    return orig_func_call;
}

/*******************************************************************

 Function: read_fact_filest::create_params_args_connection

 Inputs: fact name
  
 Outputs: the term that connects args and params of a single fact

 Purpose: 
 
\*******************************************************************/
string read_fact_filest::create_params_args_connection(string fact_name) 
{    
    string func_params_args_connection = "(and";
    std::string args = original_params_function;
    std::string params = original_params_function;
    std::string func_name = original_function_name;
    unsigned index = 0;
    while (params.find(func_name, index) != std::string::npos) 
    {
        index = params.find(func_name, index);
        params = params.replace(index, func_name.size(),fact_name);
        index += fact_name.size();
    }

    // Create a list of all input args
    std::list<std::string> args_list;
    split(args_list,args," ");
    
    // Create a list of all the in parameters
    std::list<std::string> params_list;
    split(params_list,params," ");
        
    // Add (= args params)
    assert(args_list.size() == params_list.size());
    auto it1 = args_list.begin();
    auto it2 = params_list.begin();
    
    while (it1 != args_list.end() && it2 != params_list.end())
    {
        func_params_args_connection += " (= " + (*it1) + " " + (*it2) + ")";
        it1++; it2++;
    }
    string return_val = "|" + fact_name + FUNC_RETURN + "|" ;
    string return_val_orig = "|" + func_name + FUNC_RETURN + "|" ;
    func_params_args_connection += " (= " + return_val + " " + return_val_orig + ")";
    
    func_params_args_connection +=  ")";
    // Created: (and (= |_mod#0::a!0| |mod_Cd::a!0|) (= |_mod#0::n!0| |mod_Cd::n!0|))
    
    return func_params_args_connection;
}

/*******************************************************************

 Function: read_fact_filest::::split

 Inputs: 

 Outputs: 

 Purpose: split a string according to split_str token
 
\*******************************************************************/
void read_fact_filest::split(std::list<std::string>& strings, std::string list, std::string split_str)
{
  int length=list.length();

  for(int idx=0; idx<length; idx++)
  {
    std::string::size_type next=list.find(split_str, idx);
    strings.push_back(list.substr(idx, next-idx));

    if(next==std::string::npos) break;
    idx=next;
  }
}

/*******************************************************************

 Function: read_fact_filest::write_smt_query

 Inputs: facts as a string + header of the smt file

 Outputs: smt file

 Purpose:

\*******************************************************************/
void read_fact_filest::write_smt_query(
    string facts_str, string decls_str, string base_name,
        string start_fact_name, string counter)
{
    // Write to a file: (test_path + file_no)
    ofstream smtfile;
    smtfile.open (base_name + "_" + start_fact_name + "_" + counter + "__" + std::to_string(file_no) + ".smt2");
    smtfile << decls_str;
    smtfile << facts_str;
    smtfile.close();

    // Inc the counter file_no
    file_no++;
}
