/*******************************************************************

 Module: Diff utility for 2 goto-binaries

 This class was adapted from old SAT-based evolcheck developed by G. Fedyukovich

\*******************************************************************/
#ifndef PROJECT_DIFF_H
#define PROJECT_DIFF_H

#include <time_stopping.h>
#include <goto-programs/goto_functions.h>
#include <goto-programs/read_goto_binary.h>

#include <ui_message.h>
#include "base_type.h"
#include "arith_tools.h"
#include "fixedbv.h"
#include "ieee_float.h"
#include <cstring>
#include <iostream>
#include <fstream>
#include <set>


template <class T1, class T2, class T3> struct triple
{
    typedef T1 first_type;
    typedef T2 second_type;
    typedef T3 third_type;
    
    T1 first;
    T2 second;
    T3 third;
    triple() : first(T1()), second(T2()), third(T3()) {}
    triple(const T1& x, const T2& y, const T3& z) : first(x), second(y), third(z) {}
    template <class U, class V, class W>
    triple (const triple<U,V,W> &p) : first(p.first), second(p.second), third(p.third) { }
};

typedef std::vector<triple<std::string, unsigned, const locationt*> > goto_sequencet;

class difft : public messaget{
public:
    difft(
            message_handlert &_message_handler,
            goto_functionst &_goto_functions_1,
            goto_functionst &_goto_functions_2,
            const char* _input,
            const char* _output) :
            message_handler (_message_handler),
            goto_functions_1(_goto_functions_1),
            goto_functions_2(_goto_functions_2),
            input(_input),
            output(_output),
            do_write(true),
            locs_output(false),
            old_summs(0),
            new_summs(0)
    {set_message_handler(_message_handler);};
    
    difft(
            message_handlert &_message_handler,
            goto_functionst &_goto_functions_1,
            goto_functionst &_goto_functions_2) :
            message_handler (_message_handler),
            goto_functions_1(_goto_functions_1),
            goto_functions_2(_goto_functions_2),
            input("__omega"),
            output("__omega"),
            do_write(false),
            locs_output(false),
            old_summs(0),
            new_summs(0)
    {set_message_handler(_message_handler);};
    
    bool do_diff();
    
    void set_output(const char* _output){
        // FIXME:
        //_output = "__omega";
        do_write = true;
    };
    
    void set_locs_output(){
        locs_output = true;
    }

protected:
    message_handlert &message_handler;


private:
    std::vector<std::pair<const irep_idt*, bool> > functions_old;
    
    std::vector<std::pair<const irep_idt*, bool> > functions_new;
    
    goto_functionst &goto_functions_1;
    
    goto_functionst &goto_functions_2;
    
    const char* input;
    
    const char* output;
    
    bool do_write;
    
    bool locs_output;
    
    std::set<unsigned> locs_visited;
    
    std::vector<std::string > old_summs;
    
    std::vector<std::string > new_summs;
    
    std::map<unsigned,std::vector<unsigned> > calltree_old;
    
    std::map<unsigned,std::vector<unsigned> > calltree_new;
    
    void stub_new_summs(unsigned loc);
    
    bool is_untouched(const irep_idt &name);
    
    bool unroll_goto(goto_functionst &goto_functions, const irep_idt &name,
                     goto_sequencet &goto_unrolled,
                     std::map<unsigned,std::vector<unsigned> > &calltree, unsigned init, bool inherit_change);
    
    void do_proper_diff(goto_sequencet &goto_unrolled_1,
                        goto_sequencet &goto_unrolled_2,
                        goto_sequencet &goto_common);
    
    int get_call_loc(const irep_idt& name, std::vector<std::pair<const irep_idt*, bool> >& functions, unsigned old);
    
};

#endif //PROJECT_DIFF_H
