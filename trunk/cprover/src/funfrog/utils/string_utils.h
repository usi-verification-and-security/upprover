//
// Created by Martin Blicha on 24.07.18.
//

#ifndef PROJECT_STRING_UTILS_H
#define PROJECT_STRING_UTILS_H

#include <string>
#include <vector>

std::vector<std::string> splitString(std::string s, char delim){
    std::vector<std::string> res;
    std::size_t idx = 0;
    std::size_t next = 0;
    do{
        next = s.find(delim, idx);
        res.push_back(s.substr(idx, next));
        idx = next;
        ++idx; // next points to the beginning of the found delimiter, need to move past it
    } while(next != std::string::npos);
    return res;
}

#endif //PROJECT_STRING_UTILS_H
