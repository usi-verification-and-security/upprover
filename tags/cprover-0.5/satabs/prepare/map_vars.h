/*******************************************************************\

Module: Variable Mapping HDL<->C

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#ifndef CPROVER_CEGAR_MAP_VARS_H
#define CPROVER_CEGAR_MAP_VARS_H

#include <context.h>
#include <message.h>
#include <replace_expr.h>

#include "concrete_model.h"

#if 0
void map_vars(contextt &context,
              const std::list<concrete_transition_systemt> &modules,
              replace_mapt &replace_map,
              message_handlert *message);

bool is_program_symbol(const symbolt &symbol);
#endif

#endif
