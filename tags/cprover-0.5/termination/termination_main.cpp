/********************************************************************\

 Module: Termination Checking

 Author: Daniel Kroening
         CM Wintersteiger

 Date: August 2008

\*******************************************************************/

#include <memory>

#include "termination.h"
#include "termination_bre.h"
#include "termination_direct.h"
#include "termination_path_enumeration.h"
#include "termination_cta.h"

#ifdef HAVE_INTERPOLATION
#include "termination_ita.h"
#endif

/********************************************************************\

 Function: termination

 Inputs:

 Outputs:

 Purpose: Perform Termination Check

 \*******************************************************************/

termination_resultt termination(
  termination_prover_modet mode,
  const cmdlinet &cmdline,
  const goto_functionst &goto_functions,
  const contextt &context,
  contextt &shadow_context,
  value_set_analysist &value_set_analysis,
  invariant_propagationt &invariant_propagation,
  message_handlert &message_handler,
  ui_message_handlert::uit ui,
  std::vector<exprt> &user_provided_predicates,
  unsigned max_iterations)
{  
  std::auto_ptr<termination_baset> tt;
  
  switch(mode)
  {
    case TP_BINARY_REACHABILITY: 
      tt=std::auto_ptr<termination_baset>(
            new termination_bret(cmdline, goto_functions, 
                                 context, shadow_context, 
                                 value_set_analysis, invariant_propagation,
                                 message_handler, ui));
      break;
    case TP_DIRECT:
      tt=std::auto_ptr<termination_baset>(
            new termination_directt(cmdline, goto_functions, 
                                    context, shadow_context, 
                                    value_set_analysis, invariant_propagation,
                                    message_handler, ui));
      break;
    case TP_COMPOSITIONAL:
      tt=std::auto_ptr<termination_baset>(
            new termination_ctat(cmdline, goto_functions, 
                                 context, shadow_context, 
                                 value_set_analysis, invariant_propagation,
                                 message_handler, ui));
      break;
    case TP_PATH_ENUMERATION:
      tt=std::auto_ptr<termination_baset>(
            new termination_path_enumerationt(cmdline, goto_functions, 
                                              context, shadow_context, 
                                              value_set_analysis, 
                                              invariant_propagation,
                                              message_handler, ui));
      break;
#ifdef HAVE_INTERPOLATION
    case TP_INTERPOLATING:
      tt=std::auto_ptr<termination_baset>(
            new termination_itat(cmdline, goto_functions, 
                                 context, shadow_context, 
                                 value_set_analysis, 
                                 invariant_propagation,
                                 message_handler, ui));
      break;
#endif
      
    default:
      throw ("Unknown termination prover mode.");      
  }  

  tt->user_provided_predicates=user_provided_predicates;
  tt->max_iterations=max_iterations;
  
  termination_resultt res=(*tt)();
  
  tt->show_stats();
  
  return res;
}

