
/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#include <fstream>
#include <iostream>

#include <cout_message.h>
#include <language_file.h>

#include <langapi/mode.h>

#include "lang.h"
#include "register_languages.h"

/*******************************************************************\

Function: parse_convert_file

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

typedef enum { PREPROCESS, PARSE, CONVERT } whatt;

int parse_convert_file(const cmdlinet &cmdline, whatt what)
{
  register_languages();

  if(cmdline.args.size()<1)
  {
    std::cerr << "Please specify at least one file name" << std::endl;
    return 1;
  }

  language_filest language_files;

  console_message_handlert console_message_handler;
  language_files.set_message_handler(console_message_handler);

  for(unsigned i=0; i<cmdline.args.size(); i++)
  {
    std::string filename=cmdline.args[i];

    std::ifstream infile(filename.c_str());

    if(!infile)
    {
      std::cerr << "failed to open input file " << filename << std::endl;
      return 2;
    }

    language_filet language_file;

    std::pair<language_filest::filemapt::iterator, bool>
      result=language_files.filemap.insert(
        std::pair<std::string, language_filet>(filename, language_file));

    language_filet &lf=result.first->second;
    lf.filename=filename;
    lf.language=get_language_from_filename(filename);

    if(lf.language==NULL)
    {
      std::cerr << "failed to figure out type of " << filename << std::endl;
      return 3;
    }

    languaget &language=*lf.language;

    if(what==PREPROCESS)
    {
      if(language.preprocess(infile, filename, std::cout, console_message_handler))
      {
        std::cerr << "PREPROCESSING ERROR" << std::endl;
        return 4;
      }
    }
    else
    {
      std::cerr << "Parsing " << filename << std::endl;

      if(language.parse(infile, filename, console_message_handler))
      {
        std::cerr << "PARSING ERROR" << std::endl;
        return 4;
      }

      lf.get_modules();

      if(what==PARSE)
      {
        std::cout << "Provides:" << std::endl;
        for(std::set<std::string>::const_iterator it=lf.modules.begin();
            it!=lf.modules.end(); it++)
          std::cout << "  " << *it << std::endl;

        std::cout << std::endl;

        language.show_parse(std::cout);
      }
    }
  }

  if(what==CONVERT)
  {
    contextt context;

    std::cerr << "Converting" << std::endl;

    if(language_files.typecheck(context))
    {
      std::cerr << "CONVERSION ERROR" << std::endl;
      return 5;
    }

    if(language_files.final(context))
    {
      std::cerr << "CONVERSION ERROR" << std::endl;
      return 6;
    }

    context.show(std::cout);
  }

  return 0;
}

/*******************************************************************\

Function: preprocess_lang

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int preprocess_lang(const cmdlinet &cmdline)
{
  return parse_convert_file(cmdline, PREPROCESS);
}

/*******************************************************************\

Function: parse_lang

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int parse_lang(const cmdlinet &cmdline)
{
  return parse_convert_file(cmdline, PARSE);
}

/*******************************************************************\

Function: convert_lang

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

int convert_lang(const cmdlinet &cmdline)
{
  return parse_convert_file(cmdline, CONVERT);
}
