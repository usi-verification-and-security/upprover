//
// Created by Sepideh Asadi on 2019-07-15.
//

#ifndef PROJECT_SUMMARYINVALIDEXCEPTION_H
#define PROJECT_SUMMARYINVALIDEXCEPTION_H

#include <stdexcept>

class SummaryInvalidException : std::logic_error {
public:
    SummaryInvalidException(std::string what) : std::logic_error(what)
    {}
};

#endif //PROJECT_SUMMARYINVALIDEXCEPTION_H
