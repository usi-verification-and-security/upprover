/*******************************************************************
 Module: Symex target equation which tracks different partitions for
 different deferred functions. Based on symex_target_equation.cpp.

 Author: Ondrej Sery

 \*******************************************************************/

#include <util/std_expr.h>

#include "smt_partitioning_target_equation.h"

#include "solvers/smtcheck_opensmt2.h"
#include "solvers/smt_itp.h"
#include "partition_iface.h"
#include "utils/naming_helpers.h"
#include "summary_store.h"

//#define DEBUG_ITP_SMT // ITP of SMT - testing
//#define DEBUG_ENCODING

#ifdef DISABLE_OPTIMIZATIONS
#include <fstream>
using namespace std;

#include "expr_pretty_print.h"
#endif


bool smt_partitioning_target_equationt::isRoundModelEq(const exprt &expr)
{
    if (!expr.has_operands())
        return false;
    if (expr.operands().size() > 2)
        return false;

    // Start checking if it is auto gen code for rounding model
    std::string str = id2string((expr.operands()[0]).get(ID_identifier));
    if (is_cprover_builtins_var(str))
        return true;
    
    if (expr.operands().size() < 2) return false;
    
    str = id2string((expr.operands()[1]).get(ID_identifier));
    if (is_cprover_builtins_var(str))
        return true;

    return false;
}


#ifdef DEBUG_SSA_SMT_CALL
// For the case when we have => with cast to bool condition
bool smt_partitioning_target_equationt::isTypeCastConst(const exprt &expr) {
    if (expr.id() != ID_typecast)
        return false;

    if (!expr.has_operands())
        return false;

    if (!(expr.operands())[0].is_constant())
        return false;

    // For LRA only: it will be taken care in the solver or before calling the solver
    if ((expr.operands())[0].is_boolean() ||   // in the solver
            expr.is_boolean())                 // in decider::convert
        return false;

    return true;
}
#else
bool smt_partitioning_target_equationt::isTypeCastConst(const exprt &expr) {
    throw std::logic_error("Should not be called in non-debug setting!");
}
#endif //DEBUG_SSA_SMT_CALL

//std::vector<symbol_exprt> smt_partitioning_target_equationt::fill_common_symbols(const partitiont & partition) const {
//    // call the base method, which fills the common_symbols according to computed interface of the function
//    auto common_symbols = partitioning_target_equationt::fill_common_symbols(partition);
//
//    // MB: In SMT mode, we do not care about CPROVER_rounding mode, that is needed only in PROP mode,
//    // we do not want it to leak into the signature of the summary.
//    // TODO: Would be nicer if caught earlier, e.g. do not consider it as an accessed global variable in the first place
//
//    // remove CPROVER_rounding_mode symbol from the vector, if it was part of the interface
//    assert(std::find_if(common_symbols.begin(), common_symbols.end(), [](const symbol_exprt& expr){
//        return is_cprover_rounding_mode_var(expr);
//    }) == common_symbols.end());
//    common_symbols.erase(std::remove_if(common_symbols.begin(), common_symbols.end(), [](const symbol_exprt& expr){
//        return is_cprover_rounding_mode_var(expr);
//    }),
//    common_symbols.end());
//    return common_symbols;
//}

