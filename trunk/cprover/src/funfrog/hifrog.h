/* 
 * File:   hifrog.h
 * Author: karinek
 *
 * Created on 14 July 2017, 15:55
 * 
 * All constants of HiFrog
 */

#ifndef HIFROG_H
#define HIFROG_H

#define FUNC_RETURN "#return_value!"
#define TMP_FUNC_RETURN "?return_value!::$tmp::"

#define CPROVER_BUILDINS "__CPROVER_"
#define ROUNDING_MODE "__CPROVER_rounding_mode!"
#define INITIALIZE "__CPROVER_initialize"
#define DYNAMIC_OBJ "symex_dynamic::dynamic_object"
#define GOTO_GUARD "goto_symex::\\guard#"

#define NIL "nil"
#define NONDET "nondet"
#define COUNTER "#" // GOTO to SSA (e.g., hifrog::?fun_end to hifrog::?fun_end#1)
#define SYMEX_NONDET "symex::nondet#"

#endif /* HIFROG_H */

