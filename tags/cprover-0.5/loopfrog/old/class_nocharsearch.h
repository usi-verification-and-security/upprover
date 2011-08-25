/*******************************************************************\
 
Module: loop classification for Loopfrog: string class
 
Author: Daniel Kroening
        CM Wintersteiger
 
Date: June 2007
 
\*******************************************************************/

#ifndef CLASS_NOCHARSEARCH_H_
#define CLASS_NOCHARSEARCH_H_

#include "class_base.h"

class class_nocharsearcht : public class_baset {
  public:
    class_nocharsearcht(const value_propagation_fivrt &vp);
        
    virtual void report( std::ostream& );
  
  protected:
    virtual bool recognize( const contextt&,
                   const goto_programt&, 
                   goto_programt::const_targett &,
                   goto_programt::const_targett &);
};

#endif /*CLASS_NOCHARSEARCH_H_*/
