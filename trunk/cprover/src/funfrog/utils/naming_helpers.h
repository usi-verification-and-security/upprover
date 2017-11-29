//
// Created by Martin Blicha on 30.10.17.
//

#ifndef HIFROG_NAMING_HELPERS_H
#define HIFROG_NAMING_HELPERS_H

#include <string>

struct HifrogStringConstants{
    static const std::string GLOBAL_OUT_SUFFIX;
    static const std::string GLOBAL_INPUT_SUFFIX;
    static const char SMTLIB_QUOTE;
    static const char COUNTER_SEP;
};

inline std::string add_counter(const std::string& name, int counter){
    return name + HifrogStringConstants::COUNTER_SEP + std::to_string(counter);
}

void unquote_if_necessary(std::string& name);

std::string quote(const std::string& name);

inline bool is_quoted(const std::string& name){
    return name[0] == HifrogStringConstants::SMTLIB_QUOTE && name.back() == HifrogStringConstants::SMTLIB_QUOTE;
}

void clean_name(std::string& name);

std::string removeCounter(const std::string& name);

bool contains_counter(const std::string& name);

// helper functions for dealing with names of global variables in the summaries
  inline bool isInputGlobalName(const std::string& name){
    return name.find(HifrogStringConstants::GLOBAL_INPUT_SUFFIX) != std::string::npos;
  }

  inline bool isOutputGlobalName(const std::string& name){
    return name.find(HifrogStringConstants::GLOBAL_OUT_SUFFIX) != std::string::npos;
  }

  inline bool isGlobalName(const std::string& name){
    return isInputGlobalName(name) || isOutputGlobalName(name);
  }

  std::string stripGlobalSuffix(const std::string& name);


#endif //HIFROG_NAMING_HELPERS_H
