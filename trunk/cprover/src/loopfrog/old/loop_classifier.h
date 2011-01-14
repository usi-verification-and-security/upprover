/*******************************************************************\
 
Module: loop classification for Loopfrog
 
Author: Daniel Kroening
        CM Wintersteiger
 
Date: June 2007
 
\*******************************************************************/

#ifndef LOOP_CLASSIFIER_H_
#define LOOP_CLASSIFIER_H_

#include <iostream>
#include <context.h>
#include <goto-programs/goto_functions.h>
#include <pointer-analysis/value_propagation_fivr.h>

#include "instr_string.h"
#include "instr_charsearch.h"
#include "instr_nocharsearch.h"

class loop_classifiert {
  private:
    const value_propagation_fivrt& value_prop;
    
    unsigned total_loops;
    unsigned total_statements;    
        
    instr_stringt instr_string;
    instr_charsearcht instr_charsearch;    
    instr_nocharsearcht instr_nocharsearch;
    unsigned strcmp_calls;    
    unsigned strcpy_calls;
    unsigned strcat_calls;
    unsigned strncmp_calls;    
    unsigned strncpy_calls;
    unsigned strncat_calls;
    unsigned strtok_calls;
    
  public:  
    loop_classifiert( const value_propagation_fivrt &vp ) : 
        value_prop(vp), instr_string(vp), instr_charsearch(vp),
        instr_nocharsearch(vp) {}; 
    
    void classify( const contextt&, const goto_functionst& ); 
    void classify( const contextt&, const goto_functiont& );
    
    void instrument( contextt&, goto_functionst& );
    void instrument( contextt&, goto_functiont&);
  
  private:
    void classify( const contextt&, 
                   const goto_programt&,
                   goto_programt::const_targett &,
                   goto_programt::const_targett &);
                   
    void instrument( contextt&, 
                     goto_programt&,
                     goto_programt::targett &,
                     goto_programt::targett &);
                   
          
    bool involves_strings( const contextt&, 
                           goto_programt::const_targett &,
                           goto_programt::const_targett &);
                   
    void check_call(const contextt&,
                    goto_programt::const_targett&);
                    
    void report_calls(std::ostream&);
};

#endif /*LOOP_CLASSIFIER_H_*/
