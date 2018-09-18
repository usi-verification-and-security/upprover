//
// Created by Martin Blicha on 24.07.18.
//

#ifndef PROJECT_STRING_UTILS_H
#define PROJECT_STRING_UTILS_H

#include <string>
#include <vector>

std::vector<std::string> splitString(std::string s, char delim);

std::string replace_all(std::string str, const std::string& from, const std::string& to);

#endif //PROJECT_STRING_UTILS_H
