#ifndef SUMMARYREFINER_H
#define SUMMARYREFINER_H

#include "Refiner.h"

class SummaryRefinert : public Refinert {
public:
    SummaryRefinert() {}
    
    virtual ~SummaryRefinert() {}
    
    bool refine() { return true; } // TODO
    
    bool check_spurious(SatisfyingAssignmentt cex) { assert(0); } // KE: do we use such check?
private:

};

#endif /* SUMMARYREFINER_H */

