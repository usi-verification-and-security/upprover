#ifndef PROJECT_SOLVER_H
#define PROJECT_SOLVER_H

#include <funfrog/interface/FlaRef.h>

class exprt;

class solvert
{
  public:

    virtual bool solve() = 0; // Common to all

    virtual bool is_assignment_true(FlaRef ref) const = 0;

    virtual void set_random_seed(unsigned int i) = 0;

    virtual unsigned get_random_seed() = 0;
    
    virtual exprt get_value(const exprt &expr) = 0;

    virtual bool is_overapprox_encoding() const = 0;

};
#endif //PROJECT_SOLVER_H
