/* 
 * File:   lattice_refiner_expr.cpp
 * Author: karinek
 * 
 * Created on 13 August 2017, 20:09
 */

#include "lattice_refiner_expr.h"
#include <algorithm>

//#define DEBUG_LATTICE_WALK

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
    ret.insert(current_path.begin(), current_path.end());
    
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
    
    m_is_SAT = (m_is_SAT || (refine_data.front()->childs.size() == 0));
    
    //Pop the last fact/node - going down the lattice
    lattice_refiner_modelt *front = refine_data.front();
    refine_data.pop_front(); // Remove the node we used
    
    #ifdef DEBUG_LATTICE_WALK
    std::cout << "** Finished (SAT) node " << front->get_data_str() << std::endl;
    #endif
    
    // Push facts - childs that never visited
    for (auto it : front->childs) {
        // If never check if 
        if (refined_data_UNSAT.count(it) == 0) 
        {
            refine_data.push_front(it); // Adds it to the queue to check later on
            
            #ifdef DEBUG_LATTICE_WALK
            std::cout << "** Push for later (SAT) node " << it->get_data_str() << std::endl;
            #endif
        }
    }
    
    // Pop facts
    if (m_is_SAT && no_error_trace) {
        // If cannot use the lattice at all - pop all the summaries of this lattice
        std::set<irep_idt>* to_pop = new std::set<irep_idt>();
        to_pop->insert(instantiated_facts.begin(), instantiated_facts.end());
        return to_pop;
    } else if (m_is_SAT) {
        // No pop, will use the facts to create the error trace
        return new std::set<irep_idt>();
    } else {
        // Else, remove only the facts that were with && with current facts
        return pop_facts_ids_SAT(refine_data.front());
    }
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
    // We need to pop data, since the current node is something like: x with ancestor: x&y; we remove y.    
    std::set<irep_idt> *to_pop = new std::set<irep_idt>();
    
    // Do we need to pop nodes? 
    lattice_refiner_modelt *ancestor = get_join_meet_point(curr);
    bool is_split_point = !is_fact_ids_in_data(curr);
    if (!is_split_point && (ancestor==0)) 
        return to_pop;
    
    // is a meet point?
    if (is_split_point) 
    {
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
                delete temp;
            }
        }
    }
    
    // is joint point? add the data in the diamond to pop till meet point
    while ((ancestor != 0) && (current_path.back() != ancestor)) {
        to_pop->insert(current_path.back()->data.begin(), current_path.back()->data.end());
        current_path.pop_back();
        assert(!current_path.empty()); // At least common shall be there
    }
    
    return to_pop;
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
    if (refine_data.empty()) return 0; // UNSAT globally
    
    // Marks the current node as UNSAT result
    lattice_refiner_modelt *prev_fact = refine_data.front();
    refined_data_UNSAT.insert(prev_fact);
    refine_data.pop_front(); // Remove the node we used
    
    #ifdef DEBUG_LATTICE_WALK
    std::cout << "** Finished (UNSAT) node " << prev_fact->get_data_str() << std::endl;
    #endif
    
    // Remove all nodes on a straight path to the current UNSAT node
    remove_dequed_data(prev_fact);
    if (refine_data.empty()) return 0; // UNSAT globally
    
    // what nodes to pop?
    return pop_facts_ids_UNSAT(prev_fact, refine_data.front());
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
    
            #ifdef DEBUG_LATTICE_WALK
            std::cout << "** Finished (UNSAT) node " << it->get_data_str() << std::endl;
            #endif
            
            refined_data_UNSAT.insert(*it);
            remove_dequed_data(*it); // Go up the tree
        }
    }
}


/*******************************************************************

 Function: lattice_refiner_exprt::remove_dequed_data

 Inputs: cuurent node

 Outputs: If a join, gets its meet

 Purpose: 
 
\*******************************************************************/
lattice_refiner_modelt *lattice_refiner_exprt::get_join_meet_point(lattice_refiner_modelt *curr) 
{
    lattice_refiner_modelt *common_ret = 0;
    std::set<lattice_refiner_modelt *>::iterator it = curr->ancestors.begin();
    for (auto it_next = curr->ancestors.begin(); it_next != curr->ancestors.end(); ++it_next) {
        it++;
        if (it != curr->ancestors.end()) {
            lattice_refiner_modelt *common = find_common_ancestor(*it, *it_next);
            if (common_ret == 0) common_ret = common;
            if (common_ret != common) return 0;
        }
    }
    
    return common_ret;
}
 
/*******************************************************************

 Function: lattice_refiner_exprt::is_all_childs_UNSAT

 Inputs: current location in the lattice

 Outputs: true, if all its childs leads eventually to UNSAT

 Purpose: 

\*******************************************************************/
bool lattice_refiner_exprt::is_all_childs_leads_to_UNSAT(lattice_refiner_modelt *curr) {
    // Per item in refine_data, if all its sons are in refined_data_UNSAT, remove it
    for(auto it = curr->childs.begin(); it != curr->childs.end() ; ++it) {
        if (refined_data_UNSAT.count(*it) == 0)
            return false;
    }
    
    return true;
}

/*******************************************************************

 Function: lattice_refiner_exprt::pop_facts_ids_UNSAT

 Inputs: next node in the lattice and prev node(that was UNSAT)

 Outputs: list of partitions to pop from the SSA tree

 Purpose: remove all the facts that are not in use in the next node

\*******************************************************************/
std::set<irep_idt>* lattice_refiner_exprt::pop_facts_ids_UNSAT(
            lattice_refiner_modelt *prev, lattice_refiner_modelt *curr)
{
    assert(!refine_data.empty());
    
    // Find common ancestor
    lattice_refiner_modelt *common = find_common_ancestor(prev, curr);
    assert(common);  // not null!
    
    #ifdef DEBUG_LATTICE_WALK
    std::cout << "Common ancestor is : " << common->get_data_str() << " of " <<
            prev->get_data_str() << " and " << curr->get_data_str() << std::endl;
    #endif
    
    //Pop from current_path till common
    std::set<irep_idt> *temp_facts_to_pop = new std::set<irep_idt>();
    while (current_path.back() != common) {
        lattice_refiner_modelt *curr = current_path.back();
        temp_facts_to_pop->insert(curr->data.begin(), curr->data.end());
        current_path.pop_back();
        assert(!current_path.empty()); // At least common shall be there
    }
    return temp_facts_to_pop;
}

/*******************************************************************

 Function: lattice_refiner_exprt::find_common_ancestor

 Inputs: two nodes

 Outputs: their (least) common ancestor

 Purpose:

\*******************************************************************/
lattice_refiner_modelt *lattice_refiner_exprt::find_common_ancestor(
    lattice_refiner_modelt *nodeA, lattice_refiner_modelt *nodeB) 
{
    if ((nodeA == 0) || (nodeB == 0)) return 0;
    if (nodeA->is_root()) return nodeA;
    if (nodeB->is_root()) return nodeB;
    
    // Go on the path backward and find the first node that appears as ancestor
    // of both nodeA and nodeB
    bool optimized_A = (nodeA == current_path.back()); // A is an ancestor of itself
    bool optimized_B = (nodeB == current_path.back()); // B is an ancestor of itself
    for (vector<lattice_refiner_modelt *>::reverse_iterator 
                                    itr_path = current_path.rbegin();
                                    itr_path != current_path.rend(); itr_path++) 
    {
        if ((optimized_A || is_ancestor(nodeA, *itr_path)) &&
            (optimized_B || is_ancestor(nodeB, *itr_path))) 
        {
            return *itr_path;
        }
    }
    
    return 0;
}

/*******************************************************************

 Function: lattice_refiner_exprt::is_ancestor

 Inputs: two nodes

 Outputs: check if the second node is an ancestor of the first node

 Purpose:

\*******************************************************************/
bool lattice_refiner_exprt::is_ancestor(lattice_refiner_modelt *child, lattice_refiner_modelt *ancestor) 
{
    if (child->is_root()) return ancestor->is_root(); // Assuming single root
    if (child->ancestors.find(ancestor) != child->ancestors.end()) return true;
    
    for (auto it: child->ancestors) {
        if (is_ancestor(it, ancestor)) return true;
    }
    
    return false;
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
