/*******************************************************************\

Module: Language Registration (taken from CBMC)

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <langapi/mode.h>
#include <ansi-c/ansi_c_language.h>
#include <cpp/cpp_language.h>

#ifdef HAVE_SPECC
#include <specc/specc_language.h>
#endif

#ifdef HAVE_JAVA_BYTECODE
#include <java_bytecode/java_bytecode_language.h>
#endif

#include "parser.h"

/*******************************************************************\

Function: parser_hifrogt::register_languages

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void parser_baset::register_languages()
{
  register_language(new_ansi_c_language);
  register_language(new_cpp_language);
  
  #ifdef HAVE_SPECC
  register_language(new_specc_language);
  #endif
  
  #ifdef HAVE_JAVA_BYTECODE
  register_language(new_java_bytecode_language);
  #endif
}

