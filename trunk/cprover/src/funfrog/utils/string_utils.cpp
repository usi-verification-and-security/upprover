#include"string_utils.h"

#include <algorithm>

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

// taken from https://stackoverflow.com/questions/2896600/how-to-replace-all-occurrences-of-a-character-in-string
std::string replace_all(std::string str, const std::string& from, const std::string& to) {
    size_t start_pos = 0;
    while((start_pos = str.find(from, start_pos)) != std::string::npos) {
        str.replace(start_pos, from.length(), to);
        start_pos += to.length(); // Handles case where 'to' is a substring of 'from'
    }
    return str;
}