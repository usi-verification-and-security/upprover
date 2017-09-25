/* 
 * File:   read_fact_files.cpp
 * Author: karinek
 * 
 * Created on 22 September 2017, 17:16
 */

#include "read_fact_files.h"
#include <fstream>

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
    std::ifstream input(facts_decl_file_name);
    if (!input.is_open()) 
    {
        std::cout << "Cannot find the facts's declarations file: " << facts_decl_file_name << std::endl;
        return false;
    }
    
    std::string line;
    while(std::getline(input, line)) 
    {
        decls.insert(line);
    }
    
    /* Reads the facts */
    std::ifstream input(facts_file_name);
    if (!input.is_open()) 
    {
        std::cout << "Cannot open the facts' file: " <<  facts_file_name << std::endl;
        return false;
    }

        // Read the file
    string line = "";
    
    // Name of the original function. E.g., mod
    if (!std::getline(input, line)) {
        std::cout << "Error reading original_function_name \n";
        return false;
    }
    original_function_name = line;
    std::cout << "Start loading " << facts_file_name << " function's facts: " << original_function_name << std::endl;
    
    // Declare of the original function
    if (!std::getline(input, line)) {
        std::cout << "Error reading declare_original_function \n";
        return false;
    }
    // Skip it, we don't need if for this task
    
    // Define part of the original function header
    if (!std::getline(input, line)) {
        std::cout << "Error reading original_header_function \n";
        return false;
    }
    original_header_function = line;
    
    // Define part of the original function header
    if (!std::getline(input, line)) {
        std::cout << "Error reading is_return_unsigned \n";
        return false;
    }
    // Skip it, we don't need if for this task
    
    // in/out parameters of the facts
    if (!std::getline(input, line)) {
        std::cout << "Error reading params_set_of_function \n";
        return false;
    }
    // Skip it, we don't need if for this task
    
    // Load the rest of the facts
    std::string name="";
    std::string fact="";
    std::cout << "==> Reading facts: ";
    while (std::getline(input, name)) {
        if (name[0] == ';') continue;
        
        std::cout << name << " ";
        if (!std::getline(input, fact)) {
            return false;
        }

        // Add name,fact
        facts.insert(pair<string, string> (name, fact));
    }
    std::cout << std::endl;
    
    // Complete only if load facts
    return (facts.size() > 0);
}

/*******************************************************************

 Function: read_fact_filest::save_facts_smt_queries

 Inputs: facts
  
 Outputs: sub-set of facts in smt-lib query

 Purpose: main output of the smt queries for building the lattice
 
\*******************************************************************/
void read_fact_filest::save_facts_smt_queries(string facts_query_base_file_name)
{
    // Create the declarations to the query (once to all queries)
    std::string smt_decl = "";
    for ( auto it = decls.begin(); it != decls.end(); it++ )
        smt_decl += (*it) + " \n";
    
     // Add all the facts to the file
    for (auto i = facts.begin(); i != facts.end(); ++i) 
    {
        string fact_name = i->first;
        string fact = i->second;
        
        // definition of the original function - connect to inner fact
        string orig_func_call = create_local_call_to_orig_func(fact_name);
        // Created: (= (|_mod#0| |mod_Cd::a!0| |mod_Cd::n!0|) mod_Cd::return_value!0)
        
        string orig_params_connection = create_params_args_connection(fact_name);
        // Created: (and (= |_mod#0::a!0| |mod_Cd::a!0|) (= |_mod#0::n!0| |mod_Cd::n!0|))
        
        string outter_fact = "(and " + fact + " (and " + orig_func_call + " " + orig_params_connection "))";
        
        // write fact with only one fact:
        write_smt_query(outter_fact, smt_decl, facts_query_base_file_name, fact_name, "01");
        
        for (auto j = i->begin(); j != i->end(); ++j) 
        {
        /* ... */
        }
    }
}

void read_fact_filest::write_smt_query(
    string facts_str, string decls_str, string base_name, 
        string start_fact_name, string counter)
{
    
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
    std::string params = original_header_function;
    std::string func_name = original_function_name;
    index = 0;
    while ((index = params.find(func_name, index)) != std::string::npos) {
        params = params.replace(index, func_name.size(),fact_name);
        index += fact_name.size();
    }
    string orig_func_call = " (= (|_" + func_name + "#0| " + params + ") " + return_val + ")";
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
    string func_params_args_connection = "(and ";
    std::string args = original_header_function;
    std::string params = original_header_function;
    std::string func_name = original_function_name;
    index = 0;
    while ((index = params.find(func_name, index)) != std::string::npos) {
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
        func_params_args_connection += "(= " + (*it1) + " " + (*it2) + ")"; 
    }
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
void factory_lattice_refiner_modelt::split(std::list<std::string>& strings, std::string list, std::string split_str)
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