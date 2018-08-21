//
// Created by Martin Blicha on 30.10.17.
//

#include "naming_helpers.h"
#include <cassert>
#include <algorithm>
#include <stdexcept>

namespace {
  bool is_number(const std::string & s) {
    return !s.empty() && std::find_if(s.begin(),
                                      s.end(), [](char c) { return !std::isdigit(c); }) == s.end();
  }

  void unquote(std::string & name) {
    assert(is_quoted(name));
    name.erase(name.size() - 1);
    name.erase(0, 1);
  }
}

void unquote_if_necessary(std::string & name) {
  if (is_quoted(name)) {
    unquote(name);
  }
}


std::string quote_if_necessary(std::string const & s){
    if(is_quoted(s)) return s;
    return quote(s);
}

std::string quote(const std::string & name) {
  return HifrogStringConstants::SMTLIB_QUOTE + name + HifrogStringConstants::SMTLIB_QUOTE;
}

std::string remove_counter_from_fun_name(const std::string & name) {
  auto pos = name.rfind(HifrogStringConstants::COUNTER_SEP);
  assert(pos != std::string::npos);
  assert(is_number(name.substr(pos + 1)));
  return name.substr(0, pos);
}

bool fun_name_contains_counter(const std::string & name) {
  auto pos = name.rfind(HifrogStringConstants::COUNTER_SEP);
  if (pos != std::string::npos) {
    return is_number(name.substr(pos + 1));
  }
  return false;
}

void clean_name(std::string & name) {
  unquote_if_necessary(name);
  if (fun_name_contains_counter(name)) {
    name = remove_counter_from_fun_name(name);
  }
}

std::string stripGlobalSuffix(const std::string & name) {
  if (isInputGlobalName(name)) {
    return name.substr(0, name.length() - HifrogStringConstants::GLOBAL_INPUT_SUFFIX.length());
  } else if (isOutputGlobalName(name)) {
    return name.substr(0, name.length() - HifrogStringConstants::GLOBAL_OUT_SUFFIX.length());
  }
  throw std::logic_error("stripGlobalSuffix called on a name that does not belong to global variable");
}

unsigned int get_unique_index() {
    static unsigned int index = 0;
    index += 1;
    return index;
}

const std::string HifrogStringConstants::GLOBAL_OUT_SUFFIX{"#out"};
const std::string HifrogStringConstants::GLOBAL_INPUT_SUFFIX{"#in"};
const char HifrogStringConstants::SMTLIB_QUOTE = '|';
const char HifrogStringConstants::COUNTER_SEP = '#';
const std::string HifrogStringConstants::FUN_RETURN{"#return_value"};
const std::string HifrogStringConstants::TMP_RETURN{"$tmp::return_value"};
const std::string HifrogStringConstants::CALLSTART_SYMBOL{"hifrog::fun_start"};
const std::string HifrogStringConstants::CALLEND_SYMBOL{"hifrog::fun_end"};
const std::string HifrogStringConstants::ERROR_SYMBOL{"hifrog::?err"};
const std::string HifrogStringConstants::UNSUPPORTED_VAR_NAME {"hifrog::c::unsupported_op2var"};

const std::string CProverStringConstants::INITIALIZE_METHOD{"__CPROVER_initialize"};
const std::string CProverStringConstants::IO_CONST{"symex::io::"};
const std::string CProverStringConstants::ROUNDING_MODE{"__CPROVER_rounding_mode!"};
const std::string CProverStringConstants::CPROVER_BUILDINS{"__CPROVER_"};
const std::string CProverStringConstants::DYNAMIC_OBJ{"symex_dynamic::dynamic_object"};
const std::string CProverStringConstants::GOTO_GUARD{"goto_symex::\\guard#"};
const std::string CProverStringConstants::NIL{"nil"};
const std::string CProverStringConstants::NONDETv1{"symex::"};
const std::string CProverStringConstants::NONDETv2{"symex::nondet"};
const std::string CProverStringConstants::SYMEX_NONDET{"nondet#"};

const std::string SMTConstants::SMT_BOOL{"Bool"};
const std::string SMTConstants::SMT_REAL{"Real"};
const std::string SMTConstants::SMT_UREAL{"UReal"};
const std::string SMTConstants::SMT_UNKNOWN{"?"};

const std::string HiFrogOptions::UNWIND{"unwind"};
const std::string HiFrogOptions::NO_SLICING{"no-slicing"};
const std::string HiFrogOptions::NO_ERROR_TRACE{"no-error-trace"};
const std::string HiFrogOptions::LOGIC{"logic"};



