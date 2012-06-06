/*******************************************************************\
 
Module: loop classification for Loopfrog: string class
 
Author: Daniel Kroening
        CM Wintersteiger
 
Date: June 2007
 
\*******************************************************************/

#ifndef CLASS_PATTERN1_H_
#define CLASS_PATTERN1_H_

#include "class_base.h"

class class_charsearcht : public class_baset {
  public:
    class_charsearcht(const value_propagation_fivrt &vp);
        
    virtual void report( std::ostream& );
  
  protected:
    virtual bool recognize( const contextt&,
                   const goto_programt&, 
                   goto_programt::const_targett &,
                   goto_programt::const_targett &);
};

irep_idt check_and( const exprt&, bool negated=false );
bool check_and_rec( const exprt&, 
                    bool negated,
                    std::set<exprt> &, 
                    std::set<exprt> &);

#endif /*CLASS_PATTERN1_H_*/
