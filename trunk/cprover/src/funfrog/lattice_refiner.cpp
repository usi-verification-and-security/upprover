/* 
 * File:   lattice_refinert.cpp
 * Author: karinek
 * 
 * Created on 18 July 2017, 14:21
 */

#include "lattice_refiner.h"
#include <list>

void lattice_refinert::initialize() {
    if (!is_lattice_ref_on) 
        return; // Not active if the user didn't add a model
    
    // Read the model from file
    load_models(options.get_option("load-sum-model"));
}

/*******************************************************************

 Function: lattice_refinert::load_models

 Inputs: 

 Outputs: 

 Purpose: Load all the models (according to input --load-sum-model)

\*******************************************************************/
void lattice_refinert::load_models(std::string list_of_models_fs) {

    // Supports many model-files for lattice refinement (will create several models)
    factory_lattice_refiner_modelt factory;
    std::list<std::string> model_files;
    factory.split(model_files, list_of_models_fs, ",");
    for(auto it = model_files.begin(); it != model_files.end() ; ++it)
    {
        models.insert(factory.load_model(*it));
    }
}

/*******************************************************************

 Function: lattice_refinert::can_refine

 Inputs: 

 Outputs: true if we can try to refine an instruction

 Purpose: Check if there is any instruction to refine - only if possible

\*******************************************************************/
bool lattice_refinert::can_refine(const smtcheck_opensmt2t &decider, 
                const symex_assertion_sumt& symex) const
{
    if (!is_lattice_ref_on)
        return false;
    if (!decider.has_unsupported_info() && !symex.has_missing_decl_func2refine())
        return false; // Exit, no refinement is needed! (no flag on or no abstractions done)
        
    return true;
}

/*******************************************************************

 Function: lattice_refinert::summaries_count2refine

 Inputs: 

 Outputs: how many functions we can still be refined

 Purpose: 

\*******************************************************************/
unsigned int lattice_refinert::summaries_count2refine(
        const smtcheck_opensmt2t& decider, 
        const symex_assertion_sumt& symex) const
{
    if (!can_refine(decider, symex))
        return 0;
    
    return (decider.get_unsupported_vars_count() + symex.get_miss_decl_func_count());
}

/*******************************************************************

 Function: lattice_refinert::refine

 Inputs: 

 Outputs: SMT code that connects the abstract expression to the call
 * of a summary that refines it (only to a **call**).

 Purpose: main refine, add the smt side, and it is also where we shall
 * use the lattice model to refine the code
 * 
 * Here we do: unsupported#20 = "call of the set of functions that refines it"
 * The extract of the functions (which are summaries) is done not here
 * but in refine_SSA

\*******************************************************************/
void lattice_refinert::refine(smt_partitioning_target_equationt &equation,
              symex_assertion_sumt& symex)
{
    // Shall we refine?
    if (!can_refine(decider, symex))
        return;
    
    // Start the refinement
    ++refineTryNum;
    
    #ifdef DEBUG_LATTICE 
    status () << "Start refinement with " << models.size() 
                << " lattice model(s), cycle(" << refineTryNum << ")." << eom;
    #endif
    
    // KE: TODO, find a smarter way to select the next statement to refine
    // Get all unsupported locations from the solver (candidates!) - and then check on the map
    
    // Refine functions abstracted by the solver (no OpenSMT support)
    const map<PTRef,exprt>::const_iterator begin = decider.get_itr_unsupported_info_map();
    const map<PTRef,exprt>::const_iterator end = decider.get_itr_end_unsupported_info_map();
    for (auto it = begin; it != end; it++) {   
        // if function has a definition, refine and add the refined term to a new partition
        if (get_entry_point(it->second) != SymRef_Undef) {
          decider.new_partition();  
          decider.set_to_true(refine_single_statement(it->second, it->first));
          
          decider.close_partition(); 
          //close the partition (but will solve later, after refine_SSA)
        }
    }
    
    // Refine functions abstracted by the SSA translation (no function body)
    // KE: TODO with object symex
    
} // End this cycle of refinement

/*******************************************************************

 Function: lattice_refinert::get_entry_point

 Inputs: original SSA expression we wish to refine

 Outputs: literal of the entry point
 * e.g. (declare-fun |_mod#0| (UReal UReal) UReal)

 Purpose: Add the entry point so the SSA translation can add
 * the summaries related to it - or the added one will be with meaning

\*******************************************************************/
SymRef lattice_refinert::get_entry_point(const exprt &expr)
{
    assert(models.size() > 0); // No meaning if there are no models
    std::string key_entry = gen_entry_point_name(expr);
    
    #ifdef DEBUG_LATTICE    
    status() << "Get an entry point of function " << expr.id() << " with " << expr.operands().size() << " operands" << eom;
    status() << "Function signature is " << key_entry << " key " 
            << ((declare2literal.count(key_entry) > 0) ? "exist" : "new") << "in the map" << eom;
    #endif
    
    // Check against a map
    if (declare2literal.count(key_entry) > 0) {
      return declare2literal.at(key_entry);
    }
    
    // If not in the map create it, add to the map and return it
    SymRef decl_func = SymRef_Undef;
    if (models.find(key_entry) != models.end()) {
      // Got at least one model!
      SRef in =  decider.getSMTlibDatatype(expr);
      vec<SRef> args;
      forall_operands(it, expr) {
        args.push(decider.getSMTlibDatatype(*it));
      }
      decl_func = decider.get_smt_func_decl(key_entry.c_str(), in, args);
      declare2literal.insert(pair<string, SymRef> (key_entry, decl_func));
    }

    return decl_func;
}

/*******************************************************************

 Function: lattice_refinert::gen_entry_point_name

 Inputs: original SSA expression we wish to refine

 Outputs: string with the function decl - name + operands + data types
 * e.g. (declare-fun |_mod#0| (UReal UReal) UReal) or
 * (declare-fun |_xor#0| (Bool Bool) Bool)

 Purpose: Get the key for searching entry model, note that we can have
 * two lattices for two different data type (inputs or output)

\*******************************************************************/
std::string lattice_refinert::gen_entry_point_name(const exprt &expr)
{    
    std::string key_entry(expr.id().c_str());
    key_entry = "(declare-fun |_" + key_entry + "#0| (";
    
    forall_operands(it, expr) {
        key_entry += decider.getStringSMTlibDatatype(*it) + " ";
    }
    
    key_entry += ") " + decider.getStringSMTlibDatatype(expr) + ")";
    
    return key_entry;
}
 
/*******************************************************************

 Function: lattice_refinert::refine_single_statement

 Inputs: current SSA to SMT-lib translation with its original SSA expression

 Outputs: ? maybe the new refined ptref?

 Purpose: Refine too abstract translation of the SSA to SMT-lib

\*******************************************************************/
literalt lattice_refinert::refine_single_statement(const exprt &expr, const PTRef var)
{
    status() << "Refine original translation " << decider.getPTermString(expr) 
            << " of " << expr.id() << " with " << expr.operands().size() << " operands" << eom;
    
    
    // Get next entry of refined functions
    //lattice_refiner_modelt *curr_node = get_refine_function(expr);
    
    // Create a new PTRef which refine the original expression
    PTRef refined_var; // will add a call to the refined func, e.g., mod_C3(a,n)
    //forall_operands(it, expr) {
    //    literalt param_in = decider.convert(expr);
    //    literalt arg_in;
    //   literalt bind_param = decider.set_equal(param_in, arg_in);
    //    decider.land(bind_param);
    //}
    
    // Return (= var refined_var)
    return decider.bind_var2refined_var(var, refined_var);
}

/*******************************************************************

 Function: lattice_refinert::process_SAT_result

 Inputs: 

 Outputs: 

 Purpose: if all reach to top - SAT, if SAT but not top, try the childs
 * of the current node. If reached to top (in all paths) the expression 
 * is removed from the refined data (since it cannot be refined).
 * 
 * Going down the lattice
 * 
 * If SAT according to the model - return true, else false

\*******************************************************************/
bool lattice_refinert::process_SAT_result() {  
    bool ret = false;
    for (auto it : expr2refine) {
        it.process_SAT_result();
        ret = ret || it.is_SAT();
    }
       
    return ret;
}

/*******************************************************************

 Function: lattice_refinert::process_UNSAT_result

 Inputs: 

 Outputs: 

 Purpose: change the state of the model only - the SSA changes will 
 * happen in refine_SSA, not here.
 * 
 * Going backward

\*******************************************************************/
bool lattice_refinert::process_UNSAT_result() {
    bool ret = true;
    for (auto it : expr2refine) {
        it.process_UNSAT_result();
        ret = ret && it.is_UNSAT();
    }
       
    return ret;
}

/*******************************************************************

 Function: lattice_refinert::refine_SSA

 Inputs: 

 Outputs: false if we shall continue and refining, true else.

 Purpose: move down/up in the lattice

\*******************************************************************/
bool lattice_refinert::process_solver_result(bool is_solver_ret_SAT) {
    if (is_solver_ret_SAT) {
        return process_SAT_result(); // return true if SAT
    } else {
        return process_UNSAT_result(); // return true if UNSAT
    }
    // Both will return false if there is no decision yet
}

/*******************************************************************

 Function: lattice_refinert::refine_SSA

 Inputs: the last result of the query to the solver, decider and symex objects

 Outputs: 

 Purpose: 

\*******************************************************************/
bool lattice_refinert::refine_SSA(
            const smtcheck_opensmt2t &decider, 
            symex_assertion_sumt& symex) 
{
    // Shall we refine?
    if (!can_refine(decider, symex))
        return true;
    
    // Keep all the expression we can refine, which we didn't yet kept
    ///////////////////////////////////////////////////////////////////    
    
    // 1. from the solver side
    const map<PTRef,exprt>::const_iterator begin = decider.get_itr_unsupported_info_map();
    const map<PTRef,exprt>::const_iterator end = decider.get_itr_end_unsupported_info_map();
    for (auto it = begin; it != end; it++) {   
        
    }
    
    
    // TODO:
    // Else change the encoding, maybe only to add new partitions? KE
    
    
    return false;
}