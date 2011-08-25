/*******************************************************************\
 
Module: loop instrumentation for Loopfrog: nocharsearch class
 
Author: Daniel Kroening
        CM Wintersteiger
        Aliaksei Tsitovich
 
Date: June 2007
 
\*******************************************************************/

#ifndef INSTR_NOCHARSEARCH_H_
#define INSTR_NOCHARSEARCH_H_

#include <iostream>
#include <context.h>
#include <goto-programs/goto_functions.h>
#include <pointer-analysis/value_propagation.h>

#include "instr_base.h"
#include "class_nocharsearch.h"

class instr_nocharsearcht : public instr_baset<class_nocharsearcht> {
  public:
        
    instr_nocharsearcht(const value_propagation_fivrt& vp) : 
      instr_baset<class_nocharsearcht>(vp) {};      
    virtual ~instr_nocharsearcht(void) {};
    
  protected:                   
    virtual bool instrument( contextt&,
                             goto_programt&, 
                             goto_programt::targett &,
                             goto_programt::targett &);
};

#endif /*INSTR_NOCHARSEARCH_H_*/
