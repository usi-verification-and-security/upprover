#ifndef PROJECT_SOLVER_H
#define PROJECT_SOLVER_H

class literalt;
class exprt;

class solvert
{
  public:

    virtual bool solve() = 0; // Common to all

    virtual bool is_assignment_true(literalt a) const = 0;

    virtual void set_random_seed(unsigned int i) = 0;

    virtual unsigned get_random_seed() = 0;
    
    virtual exprt get_value(const exprt &expr) = 0;

};
#endif //PROJECT_SOLVER_H
