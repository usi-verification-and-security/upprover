//
// Created by Martin Blicha on 10.09.18.
//

#ifndef PROJECT_SSA_SOLVERT_H
#define PROJECT_SSA_SOLVERT_H

#include "convertor.h"
#include "solver/solver.h"
#include "solver/interpolating_solver.h"

class ssa_solvert {
public:
    virtual ~ssa_solvert() = default;

    virtual convertort * get_convertor() { return nullptr; }

    virtual solvert * get_solver() { return nullptr; }

    virtual interpolating_solvert * get_interpolating_solver() { return nullptr; }
};
#endif //PROJECT_SSA_SOLVERT_H
