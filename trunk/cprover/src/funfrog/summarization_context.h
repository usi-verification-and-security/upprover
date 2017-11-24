/*******************************************************************

 Module: Keeps the information shared by a single summarization
 task.

 Author: Ondrej Sery

\*******************************************************************/

#ifndef CPROVER_SUMMARIZATION_CONTEXT_H
#define CPROVER_SUMMARIZATION_CONTEXT_H

//#include <iostream>
#include <fstream>
#include <pointer-analysis/value_set_analysis.h>
#include <goto-programs/goto_functions.h>
#include "summary_store.h"
#include "function_info.h"
#include "smt_summary_store.h"


// Information shared by a single summarization task.
class summarization_contextt {
public:
  summarization_contextt(
          const goto_functionst &_functions,
          const unsigned _unwind_max
          ) : 
          functions(_functions),
          unwind_max(_unwind_max),
          summary_store(NULL)
  {
    for (goto_functionst::function_mapt::const_iterator it =
            functions.function_map.begin();
            it != functions.function_map.end();
            ++it) {
      function_infos.insert(function_infost::value_type(
        it->first, function_infot(it->first)));
    }
  }
   
  // D'tor - deletes the summary storage before all         
  ~summarization_contextt() { 
      if (summary_store != NULL)
        delete summary_store;
  }
  
  const summary_idst& get_summaries(irep_idt function_id) const {
    return function_infos.find(function_id)->second.get_summaries();
  }
  
  unsigned get_unwind_max() { return unwind_max; }

  // stores prop or smt logics
  summary_storet* get_summary_store() { return summary_store; }
  void set_summary_store(summary_storet* _summary_store) { summary_store = _summary_store; }
  
  const goto_functionst& get_functions() const { return functions; }
  
  const goto_functionst::goto_functiont& get_function(
    const irep_idt& function_id) const 
  {
    return functions.function_map.find(function_id)->second;
  }
  
  const bool exist_function_info(const irep_idt& function_id) const {
      return function_infos.find(function_id) != function_infos.end();
  }
    
  const function_infot& get_function_info(const irep_idt& function_id) const {
    return function_infos.find(function_id)->second;
  }
  
  function_infot& get_function_info(const irep_idt& function_id) {
    return function_infos.find(function_id)->second;
  }

  void analyze_functions(const namespacet& ns) {
    function_infos.find(functions.entry_point())->second.analyze_globals(*this, ns);
  }

  void set_valid_summaries(const irep_idt& function_id, bool value){
    const function_infot& fun_info = get_function_info(function_id);
    const summary_idst& itps = fun_info.get_summaries();
    for (summary_idst::const_iterator it2 = itps.begin();
            it2 != itps.end(); ++it2) {
      summaryt& sum = summary_store->find_summary(*it2);
      sum.set_valid(value);
    }
  }

  bool any_invalid_summaries(const irep_idt& function_id){
    const function_infot& fun_info = get_function_info(function_id);
    const summary_idst& itps = fun_info.get_summaries();
    for (summary_idst::const_iterator it2 = itps.begin();
            it2 != itps.end(); ++it2) {
      summaryt& sum = summary_store->find_summary(*it2);
      if (!sum.is_valid()){
        return true;
      }
    }
    return false;
  }

 // KE: Here the load/store of summaries for smt/prop is not the same
 // TODO: unify the interface + fix the compact store 
  
 void deserialize_infos_prop(const std::string& file) {
    std::ifstream in;
    in.open(file.c_str());

    if (in.fail()) {
      std::cerr << "Failed to deserialize function summaries (file: " << file <<
              " cannot be read)" << std::endl;
      return;
    }

    summary_store->deserialize(in);
    function_infot::deserialize_infos(in, function_infos);

    if (in.fail()) {
      throw "Failed to load function summaries.(2)";
    }

    in.close();
  }

  void serialize_infos_prop(const std::string& file, summary_infot& summary_info) {
    summary_store->compact_store(summary_info, function_infos);
    
    std::ofstream out;
    out.open(file.c_str());

    if (out.fail()) {
      std::cerr << "Failed to serialize the function summaries (file: " << file <<
              " cannot be accessed)" << std::endl;
      return;
    }

    summary_store->serialize(out);
    function_infot::serialize_infos(out, function_infos);

    if (out.fail()) {
      throw "Failed to serialize the function summaries.";
    }

    out.close();
  }

  void deserialize_infos_smt(const std::string& file, smtcheck_opensmt2t *decider = NULL) {
    summary_store->deserialize(file, decider);
    function_infot::deserialize_infos((dynamic_cast<smt_summary_storet *> (summary_store)), function_infos);
  }

  void serialize_infos_smt(const std::string& file, summary_infot& summary_info) {
    std::ofstream out;
    out.open(file.c_str());
    serialize_infos_smt(out, summary_info);
  }

  bool serialize_infos_smt(std::ofstream &out, summary_infot& summary_info) {
    if (out.fail()) {
      std::cerr << "Failed to serialize the function summaries (file cannot be accessed)" << std::endl;
      return false;
    }

    //LA: Karine, the following line is the one that eventualyl has to be used
    //summary_store.compact_store(summary_info, function_infos);

    summary_store->serialize(out);
    if (out.fail()) {
      return false;
    }
    
    out.close();
    return true;
  }

  
private:
  const goto_functionst &functions;
  const unsigned unwind_max;
  function_infost function_infos;
  summary_storet* summary_store;
};

#endif
