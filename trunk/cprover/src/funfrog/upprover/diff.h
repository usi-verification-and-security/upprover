/*******************************************************************

 Module: Diff utility for syntactically comparing two C programs

\*******************************************************************/
#ifndef PROJECT_DIFF_H
#define PROJECT_DIFF_H

//#include <time_stopping.h>
#include <goto-programs/goto_functions.h>
#include <goto-programs/read_goto_binary.h>

#include "base_type.h"
#include "arith_tools.h"
#include "fixedbv.h"
#include "ieee_float.h"
#include <cstring>
#include <iostream>
#include <fstream>
#include <set>
#include "util/message.h"

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

typedef std::vector<triple<std::string, unsigned, const source_locationt*> > goto_sequencet;

class difft{
public:
    difft(
          messaget &_msg,
          const char* _input,
          const char* _output
         )
         :
         msg(_msg),
         input(_input),
         output(_output),
         do_write(true),     //output __omega
         locs_output(false),
         callhistory_old(0),
         callhistory_new(0)
    {};
    
    difft(
          messaget &_msg
          )
          :
          msg(_msg),
          input("__omega"),
          output("__omega"),
          do_write(false),   //output __omega
          locs_output(false),
          callhistory_old(0),
          callhistory_new(0)
    {};
    
    bool do_diff(const goto_functionst & , const goto_functionst &);
    
    void set_output(const char* _output){
        // FIXME:
        //_output = "__omega";
        do_write = true;
    };
    
    void set_locs_output(){
        locs_output = true;
    }

protected:
    messaget &msg;
    
private:
    std::vector<std::pair<const irep_idt*, bool> > functions_old;    //mapping if a function is preserved or not
    
    std::vector<std::pair<const irep_idt*, bool> > functions_new;
    
   // goto_functionst &goto_functions_1;  SA: no need to be initialized in C'tor; just pass goto_function around when needed;
                                            // then you can keep GOTO_FUNCTIONS as CONST everywhere!
   // goto_functionst &goto_functions_2;
    
    const char* input;
    
    const char* output;
    
    bool do_write;
    
    bool locs_output;   // default is false
    
    std::set<unsigned> locs_visited;
    
    std::vector<std::string > callhistory_old;
    
    std::vector<std::string > callhistory_new;
    
    std::map<unsigned,std::vector<unsigned> > calltree_old;
    
    std::map<unsigned,std::vector<unsigned> > calltree_new;
    
    void stub_new_summs(unsigned loc);
    
    bool is_untouched(const irep_idt &name);
    
    bool add_loc_info(const goto_functionst &goto_functions, const irep_idt &name,
                      goto_sequencet &goto_unrolled,
                      std::map<unsigned,std::vector<unsigned> > &calltree, unsigned init, bool inherit_change);
    
    void do_proper_diff(goto_sequencet const &goto_unrolled_1,
                        goto_sequencet const &goto_unrolled_2,
                        goto_sequencet const &goto_common);
    
    int get_call_tree_node_id(const irep_idt& new_call_name, std::vector<std::pair<const irep_idt*, bool> >& func_old, unsigned old);
    
};

//Declarations:
void collect_functions(const goto_functionst &goto_functions, const goto_programt &program,
                       std::vector<std::pair<const irep_idt*, bool> > &functions,
                       std::map<unsigned, std::vector<unsigned> > &calltree, unsigned& global_loc);

bool compare_str_vecs(goto_sequencet const &goto_unrolled_1,
                      goto_sequencet const &goto_unrolled_2,
                      goto_sequencet &goto_common);

std::string cmd_str (goto_programt::const_targett &it);

#endif //PROJECT_DIFF_H
