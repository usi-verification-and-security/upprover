//
// Created by Martin Blicha on 16.08.18.
//

#ifndef PROJECT_CONVERSION_UTILS_H
#define PROJECT_CONVERSION_UTILS_H

#include <solvers/prop/literal.h>
#include <funfrog/solvers/check_opensmt2.h>
#include <util/expr.h>

namespace hifrog {

inline literalt convert_expr(check_opensmt2t & decider, const exprt & expr) {
    return decider.convert_bool_expr(expr);
}

template<typename Iter>
void convert_guards(check_opensmt2t & decider, Iter const & beg, Iter const & end) {
    for (auto it = beg; it != end; ++it) {
        auto & ssa_step = *it;
        ssa_step.guard_literal = ssa_step.ignore ? const_literal(false)
                                                 : convert_expr(decider, ssa_step.guard);
    }
}

template<typename Iter>
void convert_assignments(check_opensmt2t & decider, Iter const & beg, Iter const & end) {
    for (auto it = beg; it != end; ++it) {
        if (it->is_assignment() && !it->ignore) {
            decider.set_to_true(it->cond_expr);
        }
    }
}

template<typename Iter>
void convert_assumptions(check_opensmt2t & decider, Iter const & beg, Iter const & end) {
    for (auto it = beg; it != end; ++it) {
        if (it->is_assume() && !it->ignore) {
            it->cond_literal = it->ignore ? const_literal(true) : convert_expr(decider, it->cond_expr);
        }
    }
}

}


#endif //PROJECT_CONVERSION_UTILS_H
