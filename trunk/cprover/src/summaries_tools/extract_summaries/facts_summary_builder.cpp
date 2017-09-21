#include "facts_summary_builder.h"
#include "facts.h"

#include "../../funfrog/hifrog.h"

#include <iostream>
#include <fstream>
using namespace std;

void facts_summary_buildert::write_summary_facts(std::string file_name, std::set<std::string> headers) {
    ofstream summary;
    summary.open (file_name);
    
    // Add extra headers if needed (as in qfuf)
    if (headers.size() > 0) { 
        for(auto it = headers.begin()++; it != headers.end() ; ++it) {
            summary << (*it) << "\n";
        }
    }
    
    // Add declare of the original function
    summary << facts.get_declare_original_function() << "\n\n";
    
    // Get the original function name - to replace later in the header
    std::string func_name = facts.get_original_function_name();
    bool is_unsigned_ret_val = facts.is_return_value_unsigned();
     
    // Add all the facts to the file
    const map<std::string,std::string>::const_iterator begin_facts = facts.get_itr_facts();
    const map<std::string,std::string>::const_iterator end_facts = facts.get_itr_end_facts();
    int def_no = 100;
    for (auto it = begin_facts; it != end_facts; it++) {
        int let_no = 0;
        string fact_name = it->first;
        string fact = it->second;
        
        // add the fact name to the header (instead of the original function name)
        string header = facts.get_original_header_function();
        std::string::size_type index = 0;
        while ((index = header.find(func_name, index)) != std::string::npos) {
            header = header.replace(index, func_name.size(), fact_name);
            index += fact_name.size();
        }
        // Created: ((|mod_Cd::a!0| Real) (|mod_Cd::n!0| Real) (|hifrog::fun_start| Bool) (|hifrog::fun_end| Bool)  (|mod_Cd::#return_value!0| Real) )  Bool
        
        
        // Return value 
        string return_val = "|" + fact_name + FUNC_RETURN + "|" ;
        string return_val_def_no = create_next_def(def_no++);
       
        string let_ret = create_let_of_facts(return_val, return_val_def_no);
        let_no++;
        // Created: (let ((?def799 |mod_Cd::#return_value!0|))
        
        
        // definition of the original function - connect to inner fact
        std::string params = facts.get_params_set_of_function();
        index = 0;
        while ((index = params.find(func_name, index)) != std::string::npos) {
            params = params.replace(index, func_name.size(),fact_name);
            index += fact_name.size();
        }
        string orig_func_def_no = create_next_def(def_no++);
        string let_orig_func_call = create_let_of_facts(
                " (= (|_" + func_name + "#0| " + params + ") " + return_val_def_no + ")", 
                orig_func_def_no);
        let_no++; 
        // Created: (let ((?def798 (= (|_mod#0| |mod_Cd::a!0| |mod_Cd::n!0|) ?def799)))
        
        
        // Fact - uses ?def and not the original return value
        index = 0;
        while ((index = fact.find(return_val, index)) != std::string::npos) {
            fact= fact.replace(index, return_val.size(),return_val_def_no);
            index += return_val_def_no.size();
        }
        string fact_def_no = create_next_def(def_no++);
        string let_fact = create_let_of_facts(fact, fact_def_no);
        let_no++;
        // Created: (let ((?def790 (=> (= |mod_Cd::n!0| |mod_Cd::a!0|) (= ?def799 0))))

        
        // start and end fun 
        string start_end_func_def_no = create_next_def(def_no++);
        string let_fun_start_end = create_let_of_facts(SUMMARY_START_END, start_end_func_def_no);
        let_no++;
        // Created: (let ((?def794 (or (not |hifrog::fun_end|) |hifrog::fun_start|)))    
        
        
        // Create unify single def (and of all the rest)                
        string temp_def2 = create_next_def(def_no++);
        string let_temp2 = create_let_of_and_of_defs(fact_def_no, start_end_func_def_no, temp_def2); 
        let_no++;
        
        string summary_def = create_next_def(def_no++);
        string summary_final_fact = ""; 
        string let_ret_unsigned = "";
        if (is_unsigned_ret_val) {
            string ret_unsigned_def = create_next_def(def_no++);
            let_ret_unsigned = create_let_of_facts(" (<= 0 "  + return_val_def_no + ")", ret_unsigned_def); 
            let_no++;
            // Create: (let ((?def989 (<= 0 |mod_Ca::#return_value!0|)))
            
            summary_final_fact = " (and " + ret_unsigned_def + 
                    create_and_of_two_defs(orig_func_def_no, temp_def2) + ")";
                    
        } else {
            summary_final_fact = create_and_of_two_defs(orig_func_def_no, temp_def2);  
        }
        string let_summary = create_let_of_facts(summary_final_fact, summary_def);
        let_no++;
        
        // Build the summary
        summary << "(define-fun |" << fact_name << "#0| " << header << "\n"
                << "    " << let_ret << "\n" 
                << "    " << let_orig_func_call << "\n" 
                << ((is_unsigned_ret_val) ? "    " : "") << let_ret_unsigned << ((is_unsigned_ret_val) ? "\n" : "") 
                << "    " << let_fact << "\n" 
                << "    " << let_fun_start_end << "\n"
                << "    " << let_temp2 << "\n"
                << "    " << let_summary << "\n\n" << summary_def << "\n)";
        
        for (int i=0; i < let_no; i++) summary << ")";
        summary << "\n\n";
    }
    
    summary.close();
}
