/*******************************************************************\
 
Module: loop instrumentation for Loopfrog: charsearch class
 
Author: Daniel Kroening
        CM Wintersteiger
        Aliaksei Tsitovich
 
Date: June 2007
 
\*******************************************************************/

#ifndef INSTR_CHARSEARCH_H_
#define INSTR_CHARSEARCH_H_

#include <iostream>
#include <context.h>
#include <goto-programs/goto_functions.h>
#include <pointer-analysis/value_propagation.h>

#include "instr_base.h"
#include "class_charsearch.h"

class instr_charsearcht : public instr_baset<class_charsearcht> {
  public:
        
    instr_charsearcht(const value_propagation_fivrt& vp) : 
      instr_baset<class_charsearcht> (vp) {};      
    virtual ~instr_charsearcht(void) {};
    
  protected:                   
    virtual bool instrument( contextt&,
                             goto_programt&, 
                             goto_programt::targett &,
                             goto_programt::targett &);
};

#endif /*INSTR_CHARSEARCH_H_*/
