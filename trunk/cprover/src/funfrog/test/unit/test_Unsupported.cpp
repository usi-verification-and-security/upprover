//
// Created by Martin Blicha on 26.08.18.
//

#include <gtest/gtest.h>
#include <funfrog/solvers/smtcheck_opensmt2_uf.h>
#include <util/expr.h>


// MB: this test tests creation of unsupported expression for the same expression in two different solvers;
TEST(test_UnsupportedFunction, test_UnsupportedFunction_TwoSolvers_SameExpression){
    solver_optionst options;
    smtcheck_opensmt2t_uf uf_solver1 {options, "test_solver1"};
    mod_exprt mod_expr{
            constant_exprt{"3", unsignedbv_typet{32}},
            constant_exprt{"2", unsignedbv_typet{32}},
    };
    (void) uf_solver1.expression_to_ptref(mod_expr);
    smtcheck_opensmt2t_uf uf_solver2 {options, "test_solver2"};
    EXPECT_NO_THROW(uf_solver2.expression_to_ptref(mod_expr));
}
