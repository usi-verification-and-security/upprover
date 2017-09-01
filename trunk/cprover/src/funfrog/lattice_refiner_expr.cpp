/* 
 * File:   lattice_refiner_expr.cpp
 * Author: karinek
 * 
 * Created on 13 August 2017, 20:09
 */

#include "lattice_refiner_expr.h"
#include <algorithm>

/*******************************************************************

 Function: lattice_refiner_exprt::get_refine_function

 Inputs: 

 Outputs: the next node in the lattice to refine the expression

 Purpose: 

\*******************************************************************/
set<lattice_refiner_modelt*> lattice_refiner_exprt::get_refine_functions() {
    set<lattice_refiner_modelt*> ret;
    ret.clear();
    if (m_is_SAT)
        return ret;

    ret.insert(refine_data.front());
    // TODO: add the whole path
    
    return ret; 
}


/*******************************************************************

 Function: lattice_refiner_exprt::process_SAT_result

 Inputs: 

 Outputs: 

 Purpose: if all reach to top - SAT, if SAT but not top, try the childs
 * of the current node. If reached to top (in all paths) the expression 
 * is removed from the refined data (since it cannot be refined).
 * 
 * Going down the lattice
 * 
 * SAT iff the current node had no childs and is SAT

\*******************************************************************/
void lattice_refiner_exprt::process_SAT_result() {
    if (refine_data.empty()) return;
    
    m_is_SAT = m_is_SAT || (refine_data.front()->childs.size() == 0);
    
    // Add the childs to the queue (if there is)
    lattice_refiner_modelt *front = refine_data.front();
    refine_data.pop_front(); // Remove the node we used
    
    for (auto it : front->childs) {
        // If never check if 
        if (refined_data_UNSAT.count(it) == 0)
            refine_data.push_front(it); // Adds it to the queue to check later on
    }
}

/*******************************************************************

 Function: lattice_refiner_exprt::process_UNSAT_result

 Inputs: 

 Outputs: 

 Purpose: 
 * 
 * Going backward, need to pop facts from the structure

\*******************************************************************/
void lattice_refiner_exprt::process_UNSAT_result() {
    if (refine_data.empty()) return;
    
    lattice_refiner_modelt *temp = refine_data.front();
    refined_data_UNSAT.insert(temp);
    refine_data.pop_front(); // Remove the node we used
    
    remove_dequed_data(temp);
    
    const std::set<irep_idt>& to_pop = pop_facts_ids(refine_data.front());
}

/*******************************************************************

 Function: lattice_refiner_exprt::remove_dequed_data

 Inputs: 

 Outputs: 

 Purpose: 
 * 
 * Remove ancestors of UNSAT nodes (iff all its childs are UNSAT).
 * 
 * Not fully optimized

\*******************************************************************/
void lattice_refiner_exprt::remove_dequed_data(lattice_refiner_modelt *curr) {
    if (refine_data.empty()) return;
    
    // Per item in refine_data, if all its sons are in refined_data_UNSAT, remove it
    for(auto it = curr->ancestors.begin(); it != curr->ancestors.end() ; ++it) {
        if (is_all_childs_leads_to_UNSAT(*it)) // All my kids goes to UNSAT - remove too 
        {
            refine_data.erase(std::remove(refine_data.begin(), refine_data.end(), *it), refine_data.end()); // Remove the node we used
            
            refined_data_UNSAT.insert(*it);
            remove_dequed_data(*it); // Go up the tree
        }
    }
}

/*******************************************************************

 Function: lattice_refiner_exprt::is_all_childs_UNSAT

 Inputs: current location in the lattice

 Outputs: true, if all its childs leads eventually to UNSAT

 Purpose: 

\*******************************************************************/
bool lattice_refiner_exprt::is_all_childs_leads_to_UNSAT(lattice_refiner_modelt *curr) {
    assert(!refine_data.empty());
    
    // Per item in refine_data, if all its sons are in refined_data_UNSAT, remove it
    for(auto it = curr->childs.begin(); it != curr->childs.end() ; ++it) {
        if (refined_data_UNSAT.count(*it) == 0)
            return false;
    }
    
    return true;
}

/*******************************************************************

 Function: lattice_refiner_exprt::pop_facts_ids

 Inputs: next node in the lattice

 Outputs: list of partitions to pop from the SSA tree

 Purpose: remove all the facts that are not in use in the next node

\*******************************************************************/
const std::set<irep_idt>& lattice_refiner_exprt::pop_facts_ids(
            lattice_refiner_modelt *curr)
{
    if (refine_data.empty()) return std::set<irep_idt>();
    
    std::set<irep_idt> temp_facts_instant;
    std::set<irep_idt> *temp_facts_to_pop =  new std::set<irep_idt>();
    
    // get all the facts we keep for the current node
    for(auto it = curr->data.begin(); it != curr->data.end() ; ++it) {
        const irep_idt& function_id = (*it).substr(0, it->size()-2);
        if (is_fact_instantiated(function_id)) {
            temp_facts_instant.insert(function_id);
        }
    } 
    
    // Get all the facts we need to pop for the current node
    for(auto it = instantiated_facts.begin(); it != instantiated_facts.end() ; ++it) {
        const irep_idt& function_id = (*it);
        if (temp_facts_instant.find(function_id) != temp_facts_instant.end()) {
            temp_facts_to_pop->insert(function_id);
            instantiated_facts.erase(function_id);
        }
    }
    
    return *temp_facts_to_pop;
}

/*******************************************************************

 Function: lattice_refiner_exprt::print_expr

 Inputs: 

 Outputs: the assignment where we going to refine an operator

 Purpose: Debug

\*******************************************************************/
std::string lattice_refiner_exprt::print_expr(smtcheck_opensmt2t &decider) {
    std::string ret;

    if (decider.getLogic()->isTrue(lhs_PTRef))
        ret = lhs.get(ID_identifier).c_str();
    else
        ret = decider.getLogic()->printTerm(lhs_PTRef);
    
    ret += " = " + refined_function + " (";

    for (auto it : call_info_operands) {
        ret += it.get(ID_identifier).c_str();
        ret += " ";
    }
    ret += ") ";

    return ret;
}


/*******************************************************************

 Function: lattice_refiner_exprt::get_lhs

 Inputs: 

 Outputs: lhs of the assume - a unique one per expression we refine
 * E.g., x = a%b, lhs is x

 Purpose: Building the injected assumes according to the lattice 

\*******************************************************************/
const exprt& lattice_refiner_exprt::get_lhs() {
    return lhs;
    // lhs is create correctly on the constuctor from expr or PTRef
}