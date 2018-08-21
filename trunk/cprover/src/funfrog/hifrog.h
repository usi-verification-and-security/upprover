#ifndef HIFROG_H
#define HIFROG_H

#include <util/ssa_expr.h>
#include <set>

#define CPROVER_BUILDINS "__CPROVER_"
#define ROUNDING_MODE "__CPROVER_rounding_mode!"
#define DYNAMIC_OBJ "symex_dynamic::dynamic_object"
#define GOTO_GUARD "goto_symex::\\guard#"
#define BUILT_IN "<built-in-additions>"

#define NIL "nil"
#define QUOTE_NIL "|nil|"
#define NONDETv1 "symex::" // Cprover nondet symbol
#define NONDETv2 "symex::nondet" // Cprover nonder symbol too
#define SYMEX_NONDET "nondet#" //"symex::nondet#" - fix to

#define SUMMARY_START_END "(and |hifrog::fun_end| (or (not |hifrog::fun_end|) |hifrog::fun_start|))"

irep_idt get_symbol_name(const exprt &expr);
std::string normalize_name(const exprt &expr);
unsigned int get_dump_current_index();
bool is_L2_SSA_symbol(const exprt& expr);
void getVarsInExpr(exprt& e, std::set<exprt>& vars);
std::string extract_expr_str_number(const exprt &expr);

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

static inline irep_idt get_symbol_L1_name(const exprt &expr) {
    return to_ssa_expr(expr).get_l1_object_identifier();
}


#endif /* HIFROG_H */

