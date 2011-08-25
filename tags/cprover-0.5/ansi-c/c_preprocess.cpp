/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

#include <stdio.h>
#include <stdlib.h>

#ifdef __LINUX__
#include <unistd.h>
#endif

#ifdef __APPLE__
#include <unistd.h>
#endif

#include <fstream>

#include <config.h>
#include <i2string.h>
#include <message_stream.h>
#include <tempfile.h>

#include "c_preprocess.h"

#define GCC_DEFINES_16 \
  " -D__INT_MAX__=32767"\
  " -D__CHAR_BIT__=8"\
  " -D__WCHAR_MAX__=32767"\
  " -D__SCHAR_MAX__=127"\
  " -D__SHRT_MAX__=32767"\
  " -D__LONG_LONG_MAX__=2147483647L"\
  " -D__LONG_MAX__=2147483647" \
  " -D__FLT_MIN__=1.17549435e-38F" \
  " -D__FLT_MAX__=3.40282347e+38F" \
  " -D__FLT_MANT_DIG__=24" \
  " -D__LDBL_MIN__=3.36210314311209350626e-4932L" \
  " -D__LDBL_MAX__=1.18973149535723176502e+4932L" \
  " -D__LDBL_MANT_DIG__=64" \
  " -D__DBL_MIN__=2.2250738585072014e-308" \
  " -D__DBL_MAX__=1.7976931348623157e+308" \
  " -D__DBL_MANT_DIG__=53" \
  " -D __SIZE_TYPE__=\"unsigned int\""\
  " -D __PTRDIFF_TYPE__=int"\
  " -D __WCHAR_TYPE__=int"\
  " -D __WINT_TYPE__=int"\
  " -D __INTMAX_TYPE__=\"long long int\""\
  " -D __UINTMAX_TYPE__=\"long long unsigned int\""

#define GCC_DEFINES_32 \
  " -D__INT_MAX__=2147483647"\
  " -D__CHAR_BIT__=8"\
  " -D__WCHAR_MAX__=2147483647"\
  " -D__SCHAR_MAX__=127"\
  " -D__SHRT_MAX__=32767"\
  " -D__LONG_LONG_MAX__=9223372036854775807LL"\
  " -D__LONG_MAX__=2147483647L" \
  " -D__FLT_MIN__=1.17549435e-38F" \
  " -D__FLT_MAX__=3.40282347e+38F" \
  " -D__FLT_MANT_DIG__=24" \
  " -D__LDBL_MIN__=3.36210314311209350626e-4932L" \
  " -D__LDBL_MAX__=1.18973149535723176502e+4932L" \
  " -D__LDBL_MANT_DIG__=64" \
  " -D__DBL_MIN__=2.2250738585072014e-308" \
  " -D__DBL_MAX__=1.7976931348623157e+308" \
  " -D__DBL_MANT_DIG__=53" \
  " -D __SIZE_TYPE__=\"long unsigned int\""\
  " -D __PTRDIFF_TYPE__=int"\
  " -D __WCHAR_TYPE__=int"\
  " -D __WINT_TYPE__=int"\
  " -D __INTMAX_TYPE__=\"long long int\""\
  " -D __UINTMAX_TYPE__=\"long long unsigned int\""
                        
#define GCC_DEFINES_LP64 \
  " -D__INT_MAX__=2147483647"\
  " -D__CHAR_BIT__=8"\
  " -D__WCHAR_MAX__=2147483647"\
  " -D__SCHAR_MAX__=127"\
  " -D__SHRT_MAX__=32767"\
  " -D__LONG_LONG_MAX__=9223372036854775807LL"\
  " -D__LONG_MAX__=9223372036854775807L"\
  " -D__FLT_MIN__=1.17549435e-38F" \
  " -D__FLT_MAX__=3.40282347e+38F" \
  " -D__FLT_MANT_DIG__=24" \
  " -D__LDBL_MIN__=3.36210314311209350626e-4932L" \
  " -D__LDBL_MAX__=1.18973149535723176502e+4932L" \
  " -D__LDBL_MANT_DIG__=64" \
  " -D__DBL_MIN__=2.2250738585072014e-308" \
  " -D__DBL_MAX__=1.7976931348623157e+308" \
  " -D__DBL_MANT_DIG__=53" \
  " -D __SIZE_TYPE__=\"long unsigned int\""\
  " -D __PTRDIFF_TYPE__=int"\
  " -D __WCHAR_TYPE__=int"\
  " -D __WINT_TYPE__=int"\
  " -D __INTMAX_TYPE__=\"long long int\""\
  " -D __UINTMAX_TYPE__=\"long long unsigned int\""

/*******************************************************************\

Function: c_preprocess

  Inputs:

 Outputs:

 Purpose: ANSI-C preprocessing

\*******************************************************************/

bool c_preprocess(
  std::istream &instream,
  const std::string &path,
  std::ostream &outstream,
  message_handlert &message_handler)
{
  // preprocessing
  message_streamt message_stream(message_handler);

  std::string file=path,
              stderr_file=get_temporary_file("tmp.stderr", ".txt");

  if(path=="") // stdin
  {
    char ch;

    file=get_temporary_file("tmp.stdin", ".c");
    FILE *tmp=fopen(file.c_str(), "wt");

    while(instream.read(&ch, 1)!=NULL)
      fputc(ch, tmp);

    fclose(tmp);
  }

  std::string command;
  
  // use VC98 CL in case of WIN32
  
  #ifdef _WIN32
  command="CL /nologo /E /D__CPROVER__";
  command+=" /D__WORDSIZE="+i2string(config.ansi_c.pointer_width);
  if(config.ansi_c.pointer_width==64)
  {
    command+=" \"/D__PTRDIFF_TYPE__=long long int\"";
    command+=" /D_WIN64"; // yes, both _WIN32 and _WIN64 get defined
  }
  else
    command+=" /D__PTRDIFF_TYPE__=int";
  #else
  command="gcc -E -undef -D__CPROVER__";

  if(config.ansi_c.os!=configt::ansi_ct::OS_WIN)
  {
    command+=" -D__null=0";
    command+=" -D__WORDSIZE="+i2string(config.ansi_c.pointer_width);
    command+=" -D__GNUC__=4";
    command+=" -D__GNUC_MINOR__=3"; // pretty arbitrary
    
    // Tell the system library which standards we support.
    // these are not gcc-default!
    //command+=" -D_POSIX_SOURCE=1 -D_POSIX_C_SOURCE=200112L";
    //command+=" -D__STRICT_ANSI__=1";

    if(config.ansi_c.int_width==16)
      command+=GCC_DEFINES_16;
    else if(config.ansi_c.int_width==32)
      command+=GCC_DEFINES_32;
    else if(config.ansi_c.int_width==64)
      command+=GCC_DEFINES_LP64;
  }
    
  
  switch(config.ansi_c.os) {
    case configt::ansi_ct::OS_LINUX:
      if(config.ansi_c.arch==configt::ansi_ct::ARCH_I386)
         command+=" -Di386 -D__i386 -D__i386__";
      else if(config.ansi_c.arch==configt::ansi_ct::ARCH_X86_64)
         command+=" -D__LP64__ -D__x86_64 -D__x86_64__ -D_LP64";
      command+=" -Dlinux -D__linux -D__linux__ -D__gnu_linux__";
      command+=" -Dunix -D__unix -D__unix__";
      command+=" -D__USE_UNIX98";
      break;
    case configt::ansi_ct::OS_MACOS:
      if(config.ansi_c.arch==configt::ansi_ct::ARCH_I386)
        command+=" -Di386 -D__i386 -D__i386__ -D__LITTLE_ENDIAN__";
      else if(config.ansi_c.arch==configt::ansi_ct::ARCH_PPC)
        command+=" -D__BIG_ENDIAN__";
      command+=" -D__APPLE__ -D__MACH__";
      // needs to be __APPLE_CPP__ for C++
      command+=" -D__APPLE_CC__";
      break;
    case configt::ansi_ct::OS_WIN:
      command+=" -D _MSC_VER=1400";
      command+=" -D _WIN32";
      command+=" -D _M_IX86=Blend";

      if(config.ansi_c.arch==configt::ansi_ct::ARCH_X86_64)
        command+=" -D _WIN64"; // yes, both _WIN32 and _WIN64 get defined

      if(config.ansi_c.char_is_unsigned)
        command+=" -D _CHAR_UNSIGNED";
      break;
    case configt::ansi_ct::NO_OS:
      command+=" -nostdinc"; // make sure we don't mess with the system library
  }
  #endif  
  
  // Standard Defines, ANSI9899 6.10.8
  std::string pre;
  #ifdef _WIN32
    pre = " /D";
  #else
    pre = " -D";
  #endif    
  command += pre + "__STDC_VERSION__=199901L";
  command += pre + "__STDC_IEC_559__=1";
  command += pre + "__STDC_IEC_559_COMPLEX__=1";
  command += pre + "__STDC_ISO_10646__=1";
  
  for(std::list<std::string>::const_iterator
      it=config.ansi_c.defines.begin();
      it!=config.ansi_c.defines.end();
      it++)
    #ifdef _WIN32
    command+=" /D \""+*it+"\"";
    #else
    command+=" -D'"+*it+"'";
    #endif

  for(std::list<std::string>::const_iterator
      it=config.ansi_c.include_paths.begin();
      it!=config.ansi_c.include_paths.end();
      it++)
    #ifdef _WIN32
    command+=" /I \""+*it+"\"";
    #else
    command+=" -I'"+*it+"'";
    #endif

  #ifndef _WIN32
  for(std::list<std::string>::const_iterator
      it=config.ansi_c.include_files.begin();
      it!=config.ansi_c.include_files.end();
      it++)
    command+=" -include '"+*it+"'";
  #endif

  #ifndef _WIN32
  for(std::list<std::string>::const_iterator
      it=config.ansi_c.preprocessor_options.begin();
      it!=config.ansi_c.preprocessor_options.end();
      it++)
    command+=" "+*it;
  #endif

  #ifdef _WIN32
  std::string tmpi=get_temporary_file("tmp.cl", ".i");
  command+=" \""+file+"\"";
  command+=" > " + tmpi;
  command+=" 2> \""+stderr_file+"\"";

  // _popen isn't very reliable on WIN32
  // that's why we use system()
  int result=system(command.c_str());

  if(path=="") unlink(file.c_str());
    
  FILE *stream=fopen(tmpi.c_str(), "r");

  if(stream!=NULL)
  {
    char ch;
    while((ch=fgetc(stream))!=EOF)
      outstream << ch;

    fclose(stream);
    unlink(tmpi.c_str());

    // errors/warnings
    {
      std::ifstream stderr_stream(stderr_file.c_str());
      while((stderr_stream.read(&ch, 1))!=NULL)
        message_stream.str << ch;
    }

    unlink(stderr_file.c_str());

    if(result!=0)
    {
      message_stream.error_parse(1);
      message_stream.error("Preprocessing failed");
      return true;
    }
    else
      message_stream.error_parse(2);
  }
  else
  {
    unlink(tmpi.c_str());
    unlink(stderr_file.c_str());
    message_stream.error("Preprocessing failed (fopen failed)");
    return true;
  }
  
  #else
  command+=" \""+file+"\"";
  command+=" 2> \""+stderr_file+"\"";

  FILE *stream=popen(command.c_str(), "r");

  if(stream!=NULL)
  {
    char ch;
    while((ch=fgetc(stream))!=EOF)
      outstream << ch;

    int result=pclose(stream);
    if(path=="") unlink(file.c_str());

    // errors/warnings
    {
      std::ifstream stderr_stream(stderr_file.c_str());
      while((stderr_stream.read(&ch, 1))!=NULL)
        message_stream.str << ch;
    }

    unlink(stderr_file.c_str());

    if(result!=0)
    {
      message_stream.error_parse(1);
      message_stream.error("Preprocessing failed");
      return true;
    }
    else
      message_stream.error_parse(2);
  }
  else
  {
    if(path=="") unlink(file.c_str());
    unlink(stderr_file.c_str());
    message_stream.error("Preprocessing failed (popen failed)");
    return true;
  }
  #endif

  return false;
}
