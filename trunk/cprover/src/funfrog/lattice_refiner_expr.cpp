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
    // TODO: add the whole path - current_path
    
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
std::set<irep_idt>* lattice_refiner_exprt::process_SAT_result() {
    if (refine_data.empty()) return 0;
    
    m_is_SAT = m_is_SAT || (refine_data.front()->childs.size() == 0);
    
    // Add the childs to the queue (if there is)
    lattice_refiner_modelt *front = refine_data.front();
    refine_data.pop_front(); // Remove the node we used
    
    for (auto it : front->childs) {
        // If never check if 
        if (refined_data_UNSAT.count(it) == 0)
            refine_data.push_front(it); // Adds it to the queue to check later on
    }
    
    // If cannot use the lattice at all - pop all the summaries of this lattice
    if (m_is_SAT && no_error_trace) {
        std::set<irep_idt>* to_pop = new std::set<irep_idt>();
        to_pop->insert(instantiated_facts.begin(), instantiated_facts.end());
        return to_pop;
    } else if (m_is_SAT) {
        return new std::set<irep_idt>();
    } else {

        // Else, remove only the facts that were with && with current facts
        return pop_facts_ids_SAT(refine_data.front());
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
std::set<irep_idt>* lattice_refiner_exprt::process_UNSAT_result() {
    if (refine_data.empty()) return 0;
    
    lattice_refiner_modelt *temp = refine_data.front();
    refined_data_UNSAT.insert(temp);
    refine_data.pop_front(); // Remove the node we used
    
    remove_dequed_data(temp);
    
    // what nodes to pop?
    return pop_facts_ids_UNSAT(refine_data.front());
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
std::set<irep_idt>* lattice_refiner_exprt::pop_facts_ids_UNSAT(
            lattice_refiner_modelt *curr)
{
    if (refine_data.empty()) return 0;
    
    std::set<irep_idt> temp_facts_instant;
    std::set<irep_idt> *temp_facts_to_pop = new std::set<irep_idt>();
    
    // get all the facts we keep for the current node
    for(auto it = curr->data.begin(); it != curr->data.end() ; ++it) {
        const irep_idt& function_id = get_function_id(*it);
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
    
    return temp_facts_to_pop;
}

/*******************************************************************

 Function: lattice_refiner_exprt::pop_facts_ids_SAT

 Inputs: next node in the lattice

 Outputs: list of partitions to pop from the SSA tree

 Purpose: remove all the facts that are not in use in the next node

\*******************************************************************/
std::set<irep_idt>* lattice_refiner_exprt::pop_facts_ids_SAT(
            lattice_refiner_modelt *curr)
{
    // Do we need to pop nodes? 
    if (!is_fact_ids_in_data(curr)) return 0;
    
    // We need to pop data, since the current node is something like: x with ancestor: x&y; we remove y.    
    std::set<irep_idt> *to_pop = new std::set<irep_idt>();
    for (auto it_p : current_path) { // per node of the path
        bool is_subtract_sets = false;
        for (auto it : curr->data) { 
            // Check if a fact from the current set was before 
            if (is_fact_ids_in_data(it_p, it)) {
                is_subtract_sets = true;
                break;
            }
        }     
        if (is_subtract_sets) {
            std::set<irep_idt>* temp = subtract_prev_data_from_facts(curr, it_p);
            to_pop->insert(temp->begin(), temp->end());
            free(temp);
        }
    }
        
    return to_pop;
}

/*******************************************************************

 Function: lattice_refiner_exprt::is_fact_ids_in_data

 Inputs: id in the format with #0 in the end

 Outputs: true if found the id in a set
 * either an id is part of prev data set => true
 * Or if the current set of ids was instantiated before (if no specific id 
 * sent)
 * in anyother case, returns false

 Purpose: 

\*******************************************************************/

bool lattice_refiner_exprt::is_fact_ids_in_data(lattice_refiner_modelt *curr, const irep_idt id)
{
    // Do we need to pop nodes? 
    int count_inst = 0; 
    for (auto it : curr->data) {
        if (id.empty()) 
            count_inst += (is_fact_instantiated(get_function_id(it)) ? 1 : 0);
        else 
            count_inst += ((id.compare(it) == 0) ? 1 : 0);
    }
    return (count_inst > 0);
}

/*******************************************************************

 Function: lattice_refiner_exprt::subtract_prev_data_from_facts

 Inputs: two lattice nodes (current and prev in the path)

 Outputs: all the facts that appears in the facts list+prev but not in curr

 Purpose: pop facts when lattice splits a&c with edges to c or a (then a node 
 * pops c, and c node pops a).

\*******************************************************************/
std::set<irep_idt>* lattice_refiner_exprt::subtract_prev_data_from_facts(
        lattice_refiner_modelt *curr,
        lattice_refiner_modelt *prev) 
{
    if (curr == 0 || prev == 0) return 0;
 
    std::set<irep_idt> *to_pop = new std::set<irep_idt>();
    for (auto it_p : prev->data) {
        bool is_exist_in_curr = false;
        for (auto it_c : curr->data) {
            if (it_c.compare(it_p) == 0) {
                is_exist_in_curr = true;
                break;
            }
        }
        if ((!is_exist_in_curr) && (is_fact_instantiated(get_function_id(it_p)))) { 
            to_pop->insert(it_p);
        }
    }
    
    
    return to_pop;
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
