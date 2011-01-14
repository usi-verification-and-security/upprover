/*******************************************************************\

Module: Termination Checking

Author: CM Wintersteiger

Date: August 2008

\*******************************************************************/

#ifndef CPROVER_TERMINATION_H
#define CPROVER_TERMINATION_H

#include <vector>

#include <expr.h>
#include <ui_message.h>

#include "termination_results.h"

/* Termination proving method */

typedef enum { TP_BINARY_REACHABILITY, /* Traditional Binary Reachability */
               TP_DIRECT, /* Direct termination proofs (Biere et al.) */
               TP_COMPOSITIONAL, /* Compositional Termination Analysis */
               TP_PATH_ENUMERATION,
               TP_INTERPOLATING, /* Interpolating Termination Analysis */
             } termination_prover_modet;

             
/* Precondition: The program passed to termination() must be instrumented 
   with termination assertions (see termination/instrumentation.h) */
               
termination_resultt
    termination(termination_prover_modet mode,
                const class cmdlinet &cmdline,
                const class goto_functionst &goto_functions,
                const class contextt &context,
                class contextt &shadow_context,
                class value_set_analysist &value_set_analysis,
                class invariant_propagationt &invariant_propagation,
                message_handlert &_mh,
                ui_message_handlert::uit ui,
                /* Options for predicate abstraction model checkers */
                std::vector<exprt> &user_provided_predicates,
                unsigned max_iterations);

#endif

