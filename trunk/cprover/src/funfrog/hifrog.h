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

//#define DEBUG_SSA_PRINT // To Enable SSA Tree print
#include <ssa_expr.h>

// For now we have only one thread any hows
#define FUNC_RETURN "::#return_value"  // KE: appears in Cprover as "#return_value"
#define TMP_FUNC_RETURN "::$tmp::return_value"
#define LATTICE_TMP_FUNC_RETURN "call__lattice::$tmp_return_value_"
#define UNSUPPORTED_VAR_NAME "hifrog::c::unsupported_op2var#"

#define CALLSTART_SYMBOL "hifrog::fun_start"
#define CALLEND_SYMBOL "hifrog::fun_end"
#define ERROR_SYMBOL "hifrog::?err"

#define CPROVER_BUILDINS "__CPROVER_"
#define ROUNDING_MODE "__CPROVER_rounding_mode!"
#define INITIALIZE "__CPROVER_initialize"
#define DYNAMIC_OBJ "symex_dynamic::dynamic_object"
#define GOTO_GUARD "goto_symex::\\guard#"

#define NONDETv1 "symex::" // Cprover nondet symbol
#define NONDETv2 "symex::nondet" // Cprover nonder symbol too
#define SYMEX_NONDET "nondet#" //"symex::nondet#" - fix to
#define IO_CONST "symex::io::" // Update according to goto_symex/symex_target_equation
#define RETURN_NIL_CPROVER "return'!0" // Check if changed; the nil (function_call.lhs().is_nil()), changed into |return'!0|

// SMT consts of datatypes, add/change here only if needed
#define SMT_BOOL "Bool"
#define SMT_REAL "Real"
#define SMT_UREAL "UReal"
#define SMT_UNKNOWN "?"

#define SUMMARY_START_END "(and |hifrog::fun_end| (or (not |hifrog::fun_end|) |hifrog::fun_start|))"

irep_idt get_symbol_name(const exprt &expr);
irep_idt get_symbol_L1_name(const exprt &expr);
bool is_hifrog_inner_symbol_name(const exprt &expr);
irep_idt extract_hifrog_inner_symbol_name(const exprt &expr);
unsigned get_symbol_L2_counter(const exprt &expr);
unsigned extract_hifrog_inner_symbol_L2_counter(const exprt &expr);
std::string fix_symex_nondet_name(const exprt &expr);
bool is_cprover_initialize_method(const std::string&);

static inline bool is_cprover_rounding_mode_var(const std::string& str)
{
    return (str.find(ROUNDING_MODE) != std::string::npos);
}

static inline bool is_cprover_rounding_mode_var(const exprt& e)
{
    return is_cprover_rounding_mode_var(id2string(e.get(ID_identifier)));
}

static inline bool is_cprover_builtins_var(const std::string str)
{
    return (str.find(CPROVER_BUILDINS) != std::string::npos);
}

static inline bool is_cprover_builtins_var(const exprt& e)
{
    return is_cprover_builtins_var(id2string(e.get(ID_identifier)));
}


#endif /* HIFROG_H */

