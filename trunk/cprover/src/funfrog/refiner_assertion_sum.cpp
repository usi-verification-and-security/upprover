/*******************************************************************

 Module: Refining schema for function summarization.
         Supposed to have different implementations.

 Author: Grigory Fedyukovich

\*******************************************************************/


#include "refiner_assertion_sum.h"

#include "subst_scenario.h"
#include "summary_store.h"


//#define DEBUG_REFINER

namespace{
    void set_valid_summaries(const summary_storet& store, const irep_idt& function_id, bool value){
        const summary_idst& itps = store.get_summaries(function_id);
        for (auto it = itps.begin();
             it != itps.end(); ++it) {
            summaryt& sum = store.find_summary(*it);
            sum.set_valid(value);
        }
    }
}

void refiner_assertion_sumt::set_inline_sum(call_tree_nodet& summary)
{
  if (summary.get_call_location() <= last_assertion_loc){
    status() << (std::string("*** REFINING function: ") + summary.get_function_id().c_str()) << eom;
    summary.set_inline();
    refined_functions.push_back(&summary);
  }
  set_valid_summaries(summary_store, summary.get_function_id(), valid);
}

void refiner_assertion_sumt::reset_inline(call_tree_nodet& summary)
{
  for (call_sitest::iterator it = summary.get_call_sites().begin();
          it != summary.get_call_sites().end(); ++it)
  {
    if ((it->second).get_precision() != INLINE){
      set_inline_sum(it->second);
      if ((it->second).is_recursion_nondet()){
          status() << "Automatically increasing unwinding bound for " << (it->second).get_function_id() << eom;
          omega.refine_recursion_call(it->second);
      }
    } else {
      reset_inline(it->second);
    }
  }
}

void refiner_assertion_sumt::reset_random(call_tree_nodet& summary)
{
  unsigned summs_size = omega.get_summaries_count();
    for (call_sitest::iterator it = summary.get_call_sites().begin();
            it != summary.get_call_sites().end(); ++it)
    {
      summary_precisiont precision = (it->second).get_precision();
      if ((precision == SUMMARY) ||    // if there were some summaries,
                                       // try to inline them first
          (precision == HAVOC && summs_size == 0)){  // and if there were not
                                                     // then refine havoced calls
        if (rand() % 1000 < 300 || rand() % 1000 > 800){
          set_inline_sum(it->second);
        }
      }
      reset_random(it->second);
                                       // TODO: we can actually try do it vice-versa
    }                                  // but due to more sophisticated choice of nondets in s_info init
                                       // there are more chances that the reason of SAT was in 2weak summaries
}

// something old
void refiner_assertion_sumt::reset_depend_rec(std::vector<call_tree_nodet*>& dep, call_tree_nodet& summary)
{
  for (call_sitest::iterator it = summary.get_call_sites().begin();
          it != summary.get_call_sites().end(); ++it)
  {
    call_tree_nodet& call = it->second;
    if (call.get_precision() != INLINE){
      for (unsigned j = 0; j < dep.size(); j++){
        if (dep[j] == &call){
          /*if (call.is_unwind_exceeded()){
            std::cout << "The call " << call.get_function_id() << " cannot be refined because the maximum unwinding bound is exceeded\n";
          } else {*/
            if (call.is_recursion_nondet()){
              status() << "Automatically increasing unwinding bound for " << call.get_function_id() << eom;
              omega.refine_recursion_call(call);
            }
            set_inline_sum(call);
            break;
          //}
        }
      }
    } else {
      reset_depend_rec(dep, call);
    }
  }
}
