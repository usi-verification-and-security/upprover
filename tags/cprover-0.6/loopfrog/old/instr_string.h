/*******************************************************************\
 
Module: loop instrumentation for Loopfrog: string class
 
Author: Daniel Kroening
        CM Wintersteiger
        Aliaksei Tsitovich
 
Date: June 2007
 
\*******************************************************************/

#ifndef INSTR_STRING_H_
#define INSTR_STRING_H_

#include <iostream>
#include <context.h>
#include <goto-programs/goto_functions.h>

#include "instr_base.h"
#include "class_string.h"

class instr_stringt : public instr_baset<class_stringt> {
  public:
        
    instr_stringt(const value_propagation_fivrt& vp) : 
      instr_baset<class_stringt>(vp)  {};      
    virtual ~instr_stringt(void) {};
                             
  protected:                   
    virtual bool instrument( contextt&,
                             goto_programt&, 
                             goto_programt::targett &,
                             goto_programt::targett &);
};

#endif /*INSTR_STRING_H_*/
