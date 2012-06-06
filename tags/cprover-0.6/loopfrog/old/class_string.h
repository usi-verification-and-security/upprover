/*******************************************************************\
 
Module: loop classification for Loopfrog: string class
 
Author: Daniel Kroening
        CM Wintersteiger
 
Date: June 2007
 
\*******************************************************************/

#ifndef CLASS_STRING_H_
#define CLASS_STRING_H_

#include <find_symbols.h>
#include "class_base.h"

class class_stringt : public class_baset {
  public:
    unsigned binsR[8], binsW[8], binsRW[8];
    unsigned recognizedR, recognizedW, recognizedRW;
    unsigned constR, constW, constRW;
    unsigned R1W1loops;
    
    class_stringt(const value_propagation_fivrt &vp);
        
    virtual void report( std::ostream& );
  
  protected:
    virtual bool recognize( const contextt&,
                   const goto_programt&, 
                   goto_programt::const_targett &,
                   goto_programt::const_targett &);
                   
  private:
    void write_loop_symbols_file( const find_symbols_sett &,
                                  const find_symbols_sett &,
                                  goto_programt::const_targett &,
                                  goto_programt::const_targett &);                                  
};

#endif /*CLASS_STRING_H_*/
