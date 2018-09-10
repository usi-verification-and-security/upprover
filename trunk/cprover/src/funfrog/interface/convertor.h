
#ifndef PROJECT_CONVERTOR_H
#define PROJECT_CONVERTOR_H

#include <util/expr.h>
#include "FlaRef.h"

#include <vector>

class convertort {
public:

    virtual FlaRef convert_bool_expr(const exprt &expr) = 0;

    virtual void set_to_true(const exprt &expr) = 0; // Common to all

    virtual void set_to_false(const exprt &expr) = 0;  // it is only used in dependency check and no-partition

    virtual void set_equal(FlaRef l1, FlaRef l2) = 0; // Common to all

    virtual FlaRef land(FlaRef l1, FlaRef l2) = 0; // Common to all

    virtual FlaRef lor(FlaRef l1, FlaRef l2) = 0;

    virtual FlaRef lor(const std::vector<FlaRef> & flas) = 0;

    virtual FlaRef limplies(FlaRef a, FlaRef b)
    {
        return lor(!a, b);
    }

    virtual FlaRef get_const_literal(bool val){
        return const_formula(val);
    }

    virtual void assert_literal(FlaRef) = 0;

    virtual FlaRef get_and_clear_var_constraints() { return const_formula(true); }

};
#endif //PROJECT_CONVERTOR_H
