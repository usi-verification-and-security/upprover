
#ifndef PROJECT_CONVERTOR_H
#define PROJECT_CONVERTOR_H

#include <util/expr.h>
#include "solvers/prop/literal.h"
#include <opensmt/opensmt2.h>

class convertort {
public:

    virtual literalt convert_bool_expr(const exprt &expr) = 0;

    virtual void set_to_true(const exprt &expr) = 0; // Common to all

    virtual void set_equal(literalt l1, literalt l2) = 0; // Common to all

    virtual literalt land(literalt l1, literalt l2) = 0; // Common to all

    virtual literalt lor(literalt l1, literalt l2) = 0;

    virtual literalt lor(const bvt & bv) = 0;

    virtual literalt limplies(literalt a, literalt b)
    {
        return lor(!a, b);
    }

    virtual literalt get_const_literal(bool val){
        return const_literal(val);
    }

    virtual void assert_literal(literalt) = 0;

    virtual literalt get_and_clear_var_constraints() { return const_literal(true); }

};
#endif //PROJECT_CONVERTOR_H
