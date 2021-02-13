//
// Created by Martin Blicha on 16.08.18.
//

#ifndef PROJECT_CONVERSION_UTILS_H
#define PROJECT_CONVERSION_UTILS_H

//#define DEBUG_SMT_ENCODING

#ifdef DEBUG_SMT_ENCODING
#include <iostream>
#endif

#include <solvers/prop/literal.h>
#include <util/expr.h>
#include <funfrog/interface/convertor.h>
#include <util/std_expr.h>

namespace hifrog {

inline FlaRef convert_expr(convertort &decider, const exprt &expr) {
    return decider.convert_bool_expr(expr);
}

template<typename Iter>
void convert_guards(convertort & decider, Iter const & beg, Iter const & end) {
    for (auto it = beg; it != end; ++it) {
        auto & ssa_step = *it;
        ssa_step.guard_literal = flaref_to_literal(ssa_step.ignore ? const_formula(false)
                                                 : convert_expr(decider, ssa_step.guard));
       // ssa_step.guard_handle = ssa_step.ignore ? false_exprt() :  ssa_step.guard;

    }
}

template<typename Iter>
void convert_assignments(convertort & decider, Iter const & beg, Iter const & end) {
    for (auto it = beg; it != end; ++it) {
        if (it->is_assignment() && !it->ignore) {
            decider.set_to_true(it->cond_expr);
#ifdef DEBUG_SMT_ENCODING
            std::cout << "************debug convert_assignments***********\n";
            std::cout << it->cond_expr.pretty() << std::endl;
            std::cout << "\n";
#endif
        }
    }
}

template<typename Iter>
void convert_assumptions(convertort & decider, Iter const & beg, Iter const & end) {
    for (auto it = beg; it != end; ++it) {
        if (it->is_assume() && !it->ignore) {
            it->cond_literal = flaref_to_literal(it->ignore ? const_formula(true) : convert_expr(decider, it->cond_expr));
        }
    }
}

}


#endif //PROJECT_CONVERSION_UTILS_H
