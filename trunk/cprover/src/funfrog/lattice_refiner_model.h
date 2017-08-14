/* 
 * File:   lattice_refiner_model.h
 * Author: karinek
 *
 * Created on 13 August 2017, 20:14
 */

#ifndef LATTICE_REFINER_MODEL_H
#define LATTICE_REFINER_MODEL_H

//#define DEBUG_LATTICE
#ifdef DEBUG_LATTICE 
#include <iostream>
#endif

#include <utility>
#include <set>
#include <list>
#include <map>
#include <string>
#include <fstream>
#include <ui_message.h>

class lattice_refiner_modelt {

public:
    lattice_refiner_modelt() { data.clear(); ancestors.clear(); childs.clear(); };
    
    std::set<std::string> data;
    std::set<lattice_refiner_modelt *> ancestors;
    std::set<lattice_refiner_modelt *> childs;

    bool is_root() { return !ancestors.size();}  // Parent is bottom
    bool is_next_top() { return !childs.size();} // Next it top
    bool has_single_child() {return (childs.size() == 1);}

    /* Gets the data of the node, e.g., mod_Cd#0,mod_Cg#0 or mod_C2not#0 */
    std::string get_data_str() {
        std::string ret = "";
        for(auto it = data.begin(); it != data.end() ; ++it) {
            if (it == data.begin())
                ret += (*it);
            else
                ret += "," + (*it);
        }
        
        return ret;
    }
    
    #ifdef DEBUG_LATTICE        
    // Print the current node
    void printNode(bool print_data_only=false) const {
            
        if (print_data_only) {
            for(auto it = data.begin(); it != data.end() ; ++it) {
                std::cout << (*it) << " && ";
            } 
            std::cout << std::endl;
        } else {
            // Print the data
            std::cout << ";; Data is: " << ((data.empty()) 
                    ? "an empty": std::to_string(data.size())) << " set : ";
            for (auto it : data) {
                std::cout << it << " && ";
            } 
            std::cout << std::endl;

            // Print the parents
            std::cout << ";; Ancestors is: " << ((ancestors.empty()) 
                    ? "an empty": std::to_string(ancestors.size())) << " set : ";
            for (auto it : ancestors) {
                it->printNode(true);
            } 
            std::cout << std::endl;

            // Print the childs
            std::cout << ";; Childs is: " << ((childs.empty()) 
                    ? "an empty": std::to_string(childs.size())) << " set : ";
            for (auto it : childs) {
                it->printNode(true);
            } 
            std::cout << std::endl;
        }
    }
    #endif
};

class factory_lattice_refiner_modelt:public messaget {
public:
    std::pair<std::string, lattice_refiner_modelt*> load_model(std::string model_file);
    void split(std::list<std::string>& strings, std::string list, std::string split_str);
    
private:
    /* Methods to load the model into the memory */
    std::string get_curr_func_decl(std::ifstream& input, std::string model_file);
    std::string get_lattice_entry_point(std::ifstream& input, std::string model_file);
    void read_file_lattice
            (std::ifstream& input, 
            std::map <std::string, lattice_refiner_modelt*>& temp_model, 
            std::map <std::string, std::list<std::string> >& helper);
    void connect_lattice_nodes(
            std::map <std::string, lattice_refiner_modelt*>& temp_model, 
            std::map <std::string, std::list<std::string> >& helper);
    

};
#endif /* LATTICE_REFINER_MODEL_H */