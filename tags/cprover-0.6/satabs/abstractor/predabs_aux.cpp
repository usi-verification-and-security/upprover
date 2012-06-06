/*******************************************************************\

Module: Predicate Abstraction Auxiliary Code

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <assert.h>

#include <simplify_expr.h>

#include <goto-programs/wp.h>
#include <langapi/language_util.h>

#include "predabs_aux.h"

/*******************************************************************\

Function: make_pos

  Inputs:

 Outputs:

 Purpose: ensures that the literal is positive
          and that all literals that are quantified over
          are unique

\*******************************************************************/

literalt make_pos(
  const namespacet &ns,
  prop_convt &conv,
  const exprt &expr)
{
  exprt tmp_expr(expr);
  literalt l=conv.convert(tmp_expr);
  literalt tmp_lit=conv.prop.new_variable();
  conv.prop.set_equal(tmp_lit, l);
  assert(!tmp_lit.sign());
  return tmp_lit;
}

/*******************************************************************\

Function: uses_symbol

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

bool uses_symbol(const exprt &expr,
                 const std::set<irep_idt> &symbols)
{
  forall_operands(it, expr)
    if(uses_symbol(*it, symbols))
      return true;

  if(expr.id()==ID_symbol)
    return symbols.find(expr.get(ID_identifier))!=symbols.end();

  return false;
}

/*******************************************************************\

Function: get_final_predicates

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

#if 0
void get_final_predicates(
  const std::vector<exprt> &predicates,
  goto_symex_statet &state,
  std::vector<exprt> &final_predicates,
  const namespacet &ns)
{
  final_predicates.resize(predicates.size());
  for(unsigned i=0; i<predicates.size(); i++)
  {
    final_predicates[i]=predicates[i];
    state.rename(final_predicates[i], ns);
    simplify(final_predicates[i], ns);
  }
}
#endif

/*******************************************************************\

Function:

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void build_equation(
  const namespacet &ns,
  const predicatest &predicates,
  goto_programt::const_targett target,
  std::list<exprt> &constraints,
  //symex_target_equationt &equation,
  //std::vector<exprt> &curr_predicates,
  //std::vector<exprt> &next_predicates,
  std::vector<exprt> &predicates_wp)
{
  constraints.clear();

  #if 0
  goto_programt::const_targett next_target;
  next_target=target;
  next_target++;

  // next_target may be end of thread
  if(!concrete_model.value_set_analysis.has_location(next_target))
    next_target=target;
  #endif

  #if 0
  optionst options;
  contextt new_context;
  abstract_dynamic_objectst abstract_dynamic_objects;
  codet tmp_code(to_code(target->code));

  abstract_dynamic_objects.collect(tmp_code);
  
  curr_predicates.resize(predicates.size());
  next_predicates.resize(predicates.size());
  #endif
  
  predicates_wp.resize(predicates.size());  

  #if 0
  for(unsigned i=0; i<predicates.size(); i++)
  {
    curr_predicates[i]=predicates[i];
    next_predicates[i]=predicates[i];
    abstract_dynamic_objects.collect(predicates[i]);
    
    //std::cout << "P " << i << " = " << from_expr(ns, "", predicates[i]) << std::endl;
    //std::cout << predicates[i].pretty() << std::endl;
  }
  #endif
  
  // done collecting, do dynamic objects
  
  #if 0
  for(unsigned i=0; i<predicates.size(); i++)
  {
    abstract_dynamic_objects.replace(curr_predicates[i]);
    abstract_dynamic_objects.replace(next_predicates[i]);
  }

  abstract_dynamic_objects.replace(tmp_code);
  #endif

  #if 0    
  goto_symex_statet state;
  state.source.pc=target;
  #endif
  
  #if 0
  {
    // find invariant set
    const invariant_sett::invariantst &invariants=
      concrete_model.invariant_propagation.lookup(target).invariants;
  
    for(invariant_sett::invariantst::expr_sett::const_iterator
        it=invariants.expr_set().begin();
        it!=invariants.expr_set().end();
        it++)
    {
      exprt tmp(*it);
      state.rename(tmp);
      constraints.push_back(tmp);
    }
  }
  #endif

  #if 0
  for(unsigned i=0; i<predicates.size(); i++)
  {
    state.rename(curr_predicates[i], ns);
    simplify(curr_predicates[i], ns);
  }

  basic_symex(tmp_code, ns, equation, state);

  for(unsigned i=0; i<predicates.size(); i++)
  {
    state.rename(next_predicates[i], ns);
    simplify(next_predicates[i], ns);
  }
  #endif
  
  for(unsigned i=0; i<predicates.size(); i++)
  {
    predicates_wp[i]=wp(target->code, predicates[i], ns);

    #if 0
    precondition(
      ns,
      concrete_model.value_set_analysis,
      next_target,
      equation, state, predicates_wp[i]);
    #endif

    //std::cout << "xp P " << i << " = " << from_expr(ns, "", predicates_wp[i]) << std::endl;
    simplify(predicates_wp[i], ns);

    //std::cout << "   P " << i << " = " << from_expr(ns, "", predicates[i]) << std::endl;
    //std::cout << "si P " << i << " = " << from_expr(ns, "", tmp) << std::endl;
    //std::cout << "wp P " << i << " = " << from_expr(ns, "", predicates_wp[i]) << std::endl;
  }
}
