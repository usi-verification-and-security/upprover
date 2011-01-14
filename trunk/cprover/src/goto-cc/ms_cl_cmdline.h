/*******************************************************************\
 
Module: A special command line object for the gcc-like options
 
Author: CM Wintersteiger
 
Date: June 2006
 
\*******************************************************************/

#ifndef GOTO_CC_MS_CL_CMDLINE_H
#define GOTO_CC_MS_CL_CMDLINE_H

#include "goto_cc_cmdline.h"

class ms_cl_cmdlinet:public goto_cc_cmdlinet
{
public:
  virtual bool parse(int, const char **);

  ms_cl_cmdlinet()
  {
    mode=MS;
  }
  
protected:
  void process_option(const std::string &s);
};

#endif /*MS_CL_CMDLINE_H_*/
