/*******************************************************************\
 
Module: loop instrumentation for Loopfrog: base class
 
Author: Daniel Kroening
        CM Wintersteiger
        Aliaksei Tsitovich
 
Date: June 2007
 
\*******************************************************************/

#ifndef INSTR_BASE_H_
#define INSTR_BASE_H_

#include <iostream>
#include <context.h>
#include <goto-programs/goto_functions.h>
#include <pointer-analysis/value_propagation_fivr.h>

#include "class_base.h"

template <class T>
class instr_baset : public T {
  public:
    instr_baset(const value_propagation_fivrt& vp) : T(vp) {};
    virtual ~instr_baset(void) {};
    
    bool classify( const contextt& c,
                   const goto_programt& p, 
                   goto_programt::const_targett & b,
                   goto_programt::const_targett & e) 
        { return T::classify(c,p,b,e); }
                   
    void report( std::ostream& s ) { T::report(s); }
    
    bool add_instrumentation( contextt& context,
                                      goto_programt& program, 
                                      goto_programt::targett &begin,
                                      goto_programt::targett &end)
    {
      goto_programt::const_targett b(begin);
      goto_programt::const_targett e(end);
      if (recognize(context, program, b, e))
        return instrument(context, program, begin, end);
      
      return false;
    };
    
  protected:                             
                   
    virtual bool instrument( 
                   contextt&,
                   goto_programt&, 
                   goto_programt::targett &,
                   goto_programt::targett &) = 0;
                   
    virtual bool recognize( const contextt &c,
                            const goto_programt &p, 
                            goto_programt::const_targett &b,
                            goto_programt::const_targett &e) 
        { return T::recognize(c,p,b,e); }
};

#endif /*INSTR_BASE_H_*/
