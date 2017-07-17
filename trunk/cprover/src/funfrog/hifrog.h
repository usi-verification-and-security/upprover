/* 
 * File:   hifrog.h
 * Author: karinek
 *
 * Created on 14 July 2017, 15:55
 * 
 * All constants of HiFrog 
 * And all things related to the interface to cprover framework
 */

#ifndef HIFROG_H
#define HIFROG_H

#include <ssa_expr.h>

// For now we have only one thread any hows
#define FUNC_RETURN "::#return_value!0"  // KE: appears in Cprover as "#return_value"
#define TMP_FUNC_RETURN "::$tmp::return_value!0"

#define CALLSTART_SYMBOL "hifrog::?fun_start";
#define CALLEND_SYMBOL "hifrog::?fun_end";
#define ERROR_SYMBOL "hifrog::?err";

#define CPROVER_BUILDINS "__CPROVER_"
#define ROUNDING_MODE "__CPROVER_rounding_mode!"
#define INITIALIZE "__CPROVER_initialize"
#define DYNAMIC_OBJ "symex_dynamic::dynamic_object"
#define GOTO_GUARD "goto_symex::\\guard#"

#define NIL "nil"
#define NONDET "symex::" // Cprover nondet symbol
#define COUNTER "#" // GOTO to SSA (e.g., hifrog::?fun_end to hifrog::?fun_end#1)
#define SYMEX_NONDET "nondet#" //"symex::nondet#"

irep_idt getSymbolName(const exprt &expr);
#endif /* HIFROG_H */

