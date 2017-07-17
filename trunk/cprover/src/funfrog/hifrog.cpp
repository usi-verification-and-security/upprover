#include "hifrog.h"

/* Get the name of an SSA expression without the instance number 
   
 * KE: please use it, as cprover framework keeps changeing all the time
 */
irep_idt getSymbolName(const exprt &expr) {
    return to_ssa_expr(expr).get_l1_object_identifier();
}