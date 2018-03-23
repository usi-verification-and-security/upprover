#ifndef THEORYREFINER_H
#define THEORYREFINER_H

#include "Refiner.h"

class TheoryRefinert : public Refinert {
public:
    TheoryRefinert() {}
    virtual ~TheoryRefinert() {}
    
    bool refine() { return true; } // TODO
    
    bool check_spurious(SatisfyingAssignmentt cex) {return false;} // TODO
    
private:

};

#endif /* THEORYREFINER_H */

