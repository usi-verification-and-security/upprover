#include "SatisfyingAssignment.h"
#include <goto-programs/goto_trace.h>
#include "../hifrog.h"

/*******************************************************************\

Function: SatisfyingAssignmentCProverFactoryt::get_vars_in_expr

  Inputs:

 Outputs:

 Purpose: Helper function for the assignment based on goto-cc/cprover framework

\*******************************************************************/
void SatisfyingAssignmentCProverFactoryt::get_vars_in_expr(exprt& e, std::set<exprt>& vars)
{
    if(e.id()==ID_symbol){
        if (!is_cprover_builtins_var(e)) vars.insert(e);
    } else if (e.has_operands()){
        for (unsigned int i = 0; i < e.operands().size(); i++){
            get_vars_in_expr(e.operands()[i], vars);
        }
    }
}

/*******************************************************************\

Function: SatisfyingAssignmentt::build_satisfying_assignment

  Inputs:

 Outputs:

 Purpose: Build the satisfying assignment for goto-cc/cprover framework
 
 Note: Currently only refers to numerical values

 * FIXME: simplify the code
\*******************************************************************/
void SatisfyingAssignmentCProverFactoryt::build_satisfying_assignment(std::vector<exprt>& exprs)
{
    std::set<exprt> vars;
    std::map<const irep_idt, std::vector<exprt>*> non_interp_classes;
    int max_interp_value = 0;

    for (auto it = exprs.begin(); it != exprs.end(); ++it)
    {
        get_vars_in_expr(*it, vars);
    }

    for (auto it = vars.begin(); it != vars.end(); ++it)
    {
        exprt val = decider->get_value(*it);

        const irep_idt val_val = val.get(ID_value);
        if (val_val.size() == 0) continue;

        int ptr;
        if (val_val[0] == 'n'){
            ptr = atoi(val_val.c_str() + 1);
		    // store the max value among n-values (will be used after the loop):
            if (ptr > max_interp_value) max_interp_value = ptr;
        } else if (val_val[0] == 'a'){
            ptr = 777; // value just for fun
        } else if (val_val[0] == 'u'){
            if (non_interp_classes.find(val_val) == non_interp_classes.end()){
                non_interp_classes[val_val] = new std::vector<exprt>();
            }
            non_interp_classes[val_val]->push_back(*it);
            // the interpretations for u-values will be computed after this loop
            continue;
        } else if (val_val == "1"){
            ptr = 1;
        } else if (val_val == "0"){
            ptr = 0;
        } else {
            ptr = atoi(val.get(ID_value).c_str());
        }

        m_model[*it] = ptr;
    }

    // computing interpretations for u-values:
    for (std::map<const irep_idt, std::vector<exprt>*>::iterator
              it=non_interp_classes.begin(); it!=non_interp_classes.end(); ++it){
        int l1 = ++max_interp_value;
        for (unsigned int i = 0; i < it->second->size(); i++){
            m_model[it->second->at(i)] = l1;
        }
    }
}

