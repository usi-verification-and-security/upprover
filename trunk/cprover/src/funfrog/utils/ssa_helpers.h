//
// Created by Martin Blicha on 14.11.17.
//

#ifndef HIFROG_SSA_HELPERS_H
#define HIFROG_SSA_HELPERS_H

#include <ostream>
#include <util/namespace.h>

template<typename C>
void print_SSA_steps(const C & iterable, const namespacet & ns, std::ostream& out)
{
  for (const auto& ssa_step : iterable){
    ssa_step.output(ns, out);
    out << '\n';
  }
}

template<typename C>
void print_SSA_steps_in_order(const C & iterable, const namespacet & ns, std::ostream& out)
{
  for (const auto& ssa_step : iterable){
    ssa_step->output(ns, out);
    out << '\n';
  }
}

#endif //HIFROG_SSA_HELPERS_H
