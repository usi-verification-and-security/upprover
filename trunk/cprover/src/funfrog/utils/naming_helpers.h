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
  static const std::string UNSUPPORTED_VAR_NAME;
};

struct SMTConstants{
    static const std::string SMT_BOOL;
    static const std::string SMT_REAL;
    static const std::string SMT_UREAL;
    static const std::string SMT_UNKNOWN;
};

struct CProverStringConstants {
    static const std::string INITIALIZE_METHOD;
    static const std::string ROUNDING_MODE;
    static const std::string IO_CONST;
    static const std::string CPROVER_BUILDINS;
    static const std::string DYNAMIC_OBJ;
    static const std::string GOTO_GUARD;
    static const std::string NIL;
    static const std::string NONDETv1;
    static const std::string NONDETv2;
    static const std::string SYMEX_NONDET;
};

struct HiFrogOptions {
    static const std::string NO_SLICING;
    static const std::string NO_ERROR_TRACE;
    static const std::string UNWIND;
    static const std::string LOGIC;
};

inline std::string add_counter_to_fun_name(const std::string & name, size_t counter) {
  return name + HifrogStringConstants::COUNTER_SEP + std::to_string(counter);
}

void unquote_if_necessary(std::string & name);

std::string quote_if_necessary(std::string const & s);

std::string quote(const std::string & name);

inline bool is_quoted(const std::string & name) {
  return name[0] == HifrogStringConstants::SMTLIB_QUOTE && name.back() == HifrogStringConstants::SMTLIB_QUOTE;
}

void clean_name(std::string & name);
//
//std::string remove_counter_from_fun_name(const std::string & name);
//
bool fun_name_contains_counter(const std::string & name);

inline bool is_cprover_initialize_method(const std::string& name)
{
  return name == CProverStringConstants::INITIALIZE_METHOD;
}

inline bool is_cprover_rounding_mode_var(const std::string& str)
{
    return (str.find(CProverStringConstants::ROUNDING_MODE) != std::string::npos);
}

inline bool is_cprover_builtins_var(const std::string str)
{
    return (str.find(CProverStringConstants::CPROVER_BUILDINS) != std::string::npos);
}

inline bool is_main(const std::string& name){
  return name == "main";
}

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

unsigned int get_unique_index();

#endif //HIFROG_NAMING_HELPERS_H
