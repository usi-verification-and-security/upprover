//
// Created by Martin Blicha on 30.10.17.
//

#ifndef HIFROG_NAMING_HELPERS_H
#define HIFROG_NAMING_HELPERS_H

#include <string>

struct HifrogStringConstants {
  static const std::string GLOBAL_OUT_SUFFIX;
  static const std::string GLOBAL_INPUT_SUFFIX;
  static const char SMTLIB_QUOTE;
  static const char COUNTER_SEP;
  static const std::string FUN_RETURN;
  static const std::string TMP_RETURN;
  static const std::string CALLSTART_SYMBOL;
  static const std::string CALLEND_SYMBOL;
  static const std::string ERROR_SYMBOL;
};

struct CProverStringConstants {
  static const std::string INITIALIZE_METHOD;
  static const std::string IO_CONST;
};

inline std::string add_counter_to_fun_name(const std::string & name, size_t counter) {
  return name + HifrogStringConstants::COUNTER_SEP + std::to_string(counter);
}

void unquote_if_necessary(std::string & name);

std::string quote(const std::string & name);

inline bool is_quoted(const std::string & name) {
  return name[0] == HifrogStringConstants::SMTLIB_QUOTE && name.back() == HifrogStringConstants::SMTLIB_QUOTE;
}

void clean_name(std::string & name);
//
//std::string removeCounter(const std::string & name);
//
bool fun_name_contains_counter(const std::string & name);

inline bool is_cprover_initialize_method(const std::string& name)
{
  return name == CProverStringConstants::INITIALIZE_METHOD;
}
inline bool is_main(const std::string& name){
  return name == "main";
}

#endif //HIFROG_NAMING_HELPERS_H
