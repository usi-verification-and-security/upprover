#ifndef LATTICEREFINER_H
#define LATTICEREFINER_H

#include "Refiner.h"
class LatticeRefinert : public Refinert {
public:
    LatticeRefinert() {}
    virtual ~LatticeRefinert() {}
    
    bool refine() { return true; } // TODO
    
    bool check_spurious(SatisfyingAssignmentt cex) {return false;} // TODO

private:

};

#endif /* LATTICEREFINER_H */

