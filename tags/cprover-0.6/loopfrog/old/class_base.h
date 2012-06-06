/*******************************************************************\
 
Module: loop classification for Loopfrog: classification class base class
 
Author: Daniel Kroening
        CM Wintersteiger
 
Date: June 2007
 
\*******************************************************************/

#ifndef CLASS_BASE_H_
#define CLASS_BASE_H_

#include <iostream>
#include <context.h>
#include <goto-programs/goto_functions.h>
#include <pointer-analysis/value_propagation_fivr.h>

class class_baset {
  protected:
    const value_propagation_fivrt& value_prop;
    
  public:
    unsigned recognized;    
        
    class_baset(const value_propagation_fivrt& vp) : value_prop(vp) 
      { recognized=0; };
    virtual ~class_baset(void) {};
    
    bool classify( const contextt&,
                   const goto_programt&, 
                   goto_programt::const_targett &,
                   goto_programt::const_targett &);
                   
    virtual void report( std::ostream& );
    
  protected:    
                   
    virtual void save_loop( const std::string&,     
                    const contextt &context,               
                    const goto_programt&, 
                    goto_programt::const_targett &,
                    goto_programt::const_targett &) const;
                    
    virtual bool recognize( const contextt&,
                   const goto_programt&, 
                   goto_programt::const_targett &,
                   goto_programt::const_targett &) = 0;
};

#endif /*CLASS_BASE_H_*/
