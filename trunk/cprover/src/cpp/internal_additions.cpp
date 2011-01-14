/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <config.h>

#include <ansi-c/internal_additions.h>
#include <ansi-c/gcc_builtin_headers.h>

#include "internal_additions.h"

/*******************************************************************\

Function: c2cpp

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

std::string c2cpp(const std::string &s)
{
  std::string result;
  
  result.reserve(s.size());
  
  for(unsigned i=0; i<s.size(); i++)
  {
    char ch=s[i];
    
    if(ch=='_' && std::string(s, i, 5)=="_Bool")
    {
      result.append("bool");
      i+=4;
      continue;
    }
    
    result+=ch;
  }
  
  return result;
}

/*******************************************************************\

Function: cpp_interal_additions

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void cpp_internal_additions(std::ostream &out)
{
  out << "# 1 \"<built-in>\"" << std::endl;

  // __CPROVER namespace
  out << "namespace __CPROVER { }" << std::endl;
  
  // types
  out << "typedef __typeof__(sizeof(int)) __CPROVER::size_t;" << std::endl;

  // assume/assert
  out << "extern \"C\" void assert(bool assertion);" << std::endl;
  out << "extern \"C\" void __CPROVER_assume(bool assumption);" << std::endl;
  out << "extern \"C\" void __CPROVER_assert("
         "bool assertion, const char *description);" << std::endl;
  out << "void __CPROVER::assume(bool assumption);" << std::endl;
  out << "void __CPROVER::assert("
         "bool assertion, const char *description);" << std::endl;

  // CPROVER extensions
  out << "extern \"C\" const unsigned __CPROVER::constant_infinity_uint;" << std::endl;
  out << "extern \"C\" void __CPROVER_initialize();" << std::endl;
  out << "extern \"C\" void __CPROVER_input(const char *id, ...);" << std::endl;

  // for dynamic objects
  out << "extern \"C\" bool __CPROVER_alloc[__CPROVER::constant_infinity_uint];" << std::endl;
  out << "extern \"C\" __CPROVER::size_t __CPROVER_alloc_size[__CPROVER::constant_infinity_uint];" << std::endl;

  // float
  out << "extern \"C\" int __CPROVER_rounding_mode;" << std::endl;      

  // arrays
  out << "bool __CPROVER::array_equal(const void array1[], const void array2[]);" << std::endl;
  out << "void __CPROVER::array_copy(const void dest[], const void src[]);" << std::endl;
            
  // GCC stuff
  out << "extern \"C\" {" << std::endl;
  out << c2cpp(GCC_BUILTIN_HEADERS);
  out << "}" << std::endl;
  
  if(config.ansi_c.os==configt::ansi_ct::OS_WIN)
    out << "extern \"C\" int __noop(...);\n"; // this is Visual C/C++    

  std::string architecture_strings;
  ansi_c_architecture_strings(architecture_strings);
  
  out << "extern \"C\" {" << std::endl;
  out << architecture_strings;
  out << "}" << std::endl;
}

