/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#include <langapi/mode.h>

#include "register_languages.h"

#include <ansi-c/ansi_c_language.h>

#ifdef HAVE_CPP
#include <cpp/cpp_language.h>
#endif

#ifdef HAVE_SPECC
#include <specc/specc_language.h>
#endif

#ifdef HAVE_SMV
#include <smvlang/smv_language.h>
#endif

#ifdef HAVE_VERILOG
#include <verilog/verilog_language.h>
#endif

#ifdef HAVE_MDLLANG
#include <mdl/mdl_language.h>
#endif

/*******************************************************************\

Function: register_languages

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void register_languages()
{
  register_language(new_ansi_c_language);
  
  #ifdef HAVE_CPP
  register_language(new_cpp_language);
  #endif
  
  #ifdef HAVE_SPECC
  register_language(new_specc_language);
  #endif

  #ifdef HAVE_SMV
  register_language(new_smv_language);
  #endif
  
  #ifdef HAVE_VERILOG
  register_language(new_verilog_language);
  #endif

  #ifdef HAVE_MDLLANG
  register_language(new_mdl_language);
  #endif
}
