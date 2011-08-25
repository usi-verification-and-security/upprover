/*******************************************************************\

Module:

Author: Daniel Kroening, kroening@cs.cmu.edu

\*******************************************************************/

#ifndef CPROVER_LANG_H
#define CPROVER_LANG_H

#include <cmdline.h>

int parse_lang(const cmdlinet &cmdline);
int preprocess_lang(const cmdlinet &cmdline);
int convert_lang(const cmdlinet &cmdline);

#endif
