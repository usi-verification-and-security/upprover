#include "lattice_refiner_model.h"

using namespace std;

/*******************************************************************

 Function: factory_lattice_refiner_modelt::load_model

 Inputs: file name where the model is -  one model in a file

 Outputs: add new model to the map of models per function

 Purpose: load a model from a single file

\*******************************************************************/
std::pair<string, lattice_refiner_modelt*> factory_lattice_refiner_modelt::load_model(
            std::string model_file) 
{
    std::ifstream input(model_file);
    
    /* Key is the function declaration in SMT-lib format */
    string func_decl_smt = get_curr_func_decl(input, model_file);
    
    /* Mark the bottom of the lattice */
    std::string child_of_bot = get_lattice_entry_point(input, model_file);
    
    /* Does have all the headers? */
    assert(!func_decl_smt.empty() && !child_of_bot.empty() && "Data of the lattice input file is corrupted");
    
    /* Read the lattice */
    map <string, lattice_refiner_modelt*> temp_model;
    map <string, list<string> > helper;
    read_file_lattice(input, temp_model, helper);
    
    /* Fix the links in the lattice */
    connect_lattice_nodes(temp_model, helper);
    
    /* Create the model */
    lattice_refiner_modelt* root = (temp_model.find(child_of_bot))->second;
    
    /* Add the model to the models container */
    return (std::pair<string, lattice_refiner_modelt*> (func_decl_smt, root));
}

/*******************************************************************

 Function: factory_lattice_refiner_modelt::get_curr_func_decl

 Inputs: 

 Outputs: 

 Purpose: 

\*******************************************************************/
string factory_lattice_refiner_modelt::get_curr_func_decl(ifstream& input, string model_file)
{
    /* Key is the function declaration in SMT-lib format */
    string func_decl_smt = "";
    if (!std::getline(input, func_decl_smt)) {
        status () << "Cannot load model in file: " << model_file << eom;
    }
    
    return func_decl_smt;   
}

/*******************************************************************

 Function: factory_lattice_refiner_modelt::get_lattice_entry_point

 Inputs: 

 Outputs: 

 Purpose: 

\*******************************************************************/
string factory_lattice_refiner_modelt::get_lattice_entry_point(ifstream& input, string model_file)
{
    /* Mark the bottom of the lattice */
    std::string child_of_bot = "";
    if (!std::getline(input, child_of_bot)) {
        status () << "Cannot load model in file: " << model_file << eom;
    } 
    
    return child_of_bot;
}

/*******************************************************************

 Function: factory_lattice_refiner_modelt::read_file_lattice

 Inputs: 

 Outputs: 

 Purpose: 

\*******************************************************************/
void factory_lattice_refiner_modelt::read_file_lattice(ifstream& input, 
        map <string, lattice_refiner_modelt*>& temp_model, map <string, list<string> >& helper)
{
    /* Read the lattice */    
    string node_data;
    helper.clear();
    temp_model.clear();
    
    while(std::getline(input, node_data)) {
        std::list<std::string> data_list;
        split(data_list,node_data,",");
        
        /* Create the current node with (only) its data */
        lattice_refiner_modelt* temp_node = new lattice_refiner_modelt();
        std::list<std::string> temp_data4node;    
        std::string key = data_list.front(); // Take the first item
        split(temp_data4node, key, ";");
        temp_node->data.insert(temp_data4node.begin(), temp_data4node.end());
        temp_model.insert(pair<string, lattice_refiner_modelt*> (key, temp_node));
        
        #ifdef DEBUG_LATTICE   
        // To test the keys (data) is not corrupted
        std::cout << ";;;;; Add new node ! " << key << "(" << node_data 
                << "), size (" << temp_data4node.size() << ")" << std::endl;
        temp_node->printNode();
        #endif
        
         /* Keep the childs for later */
        if (data_list.size() > 1) {
            data_list.pop_front();
            helper.insert(pair<string, list<string> > (key, data_list));
        }
    }
}

/*******************************************************************

 Function: factory_lattice_refiner_modelt::connect_lattice_nodes

 Inputs: 

 Outputs: 

 Purpose: 

\*******************************************************************/
void factory_lattice_refiner_modelt::connect_lattice_nodes(
    map <string, lattice_refiner_modelt*>& temp_model, map <string, list<string> >& helper)
{
    /* Fix the links in the lattice */
    for(auto it = helper.begin()++; it != helper.end() ; ++it) {
        std::string key = it->first;
        lattice_refiner_modelt* parent = (temp_model.find(key))->second;
        assert(parent != 0);
        
        for(auto it2 = it->second.begin(); it2 != it->second.end() ; ++it2) {
            // Conenct a child to a parent
            lattice_refiner_modelt* child = (temp_model.find(*it2))->second;            
            assert(child != 0);
            parent->childs.insert(child);
            child->ancestors.insert(parent);
        }
        
    }
}

/*******************************************************************

 Function: factory_lattice_refiner_modelt::split

 Inputs: 

 Outputs: Returns a list of summary files 

 Purpose: split the input into a list of file names

\*******************************************************************/
void factory_lattice_refiner_modelt::split(std::list<std::string>& strings, std::string list, std::string split_str){

  int length=list.length();

  for(int idx=0; idx<length; idx++)
  {
    std::string::size_type next=list.find(split_str, idx);
    strings.push_back(list.substr(idx, next-idx));

    if(next==std::string::npos) break;
    idx=next;
  }
}
