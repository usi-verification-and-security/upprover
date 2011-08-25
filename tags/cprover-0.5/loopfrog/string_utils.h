/*******************************************************************\
 
Module: loop classification for Loopfrog: helpers
 
Author: Daniel Kroening
        CM Wintersteiger
 
Date: June 2007
 
\*******************************************************************/

#ifndef STRING_UTILS_H_
#define STRING_UTILS_H_

#include <expr.h>
#include <type.h>
#include <find_symbols.h>
#include <pointer-analysis/value_set.h>

bool find_string_type(const exprt&);
bool find_string_type_symbols(  const exprt&, 
                                const value_sett&, 
                                find_symbols_sett&);
bool is_string_type(const typet&);
bool is_char_type(const typet&);
bool is_int_type(const typet& type);
void find_symbols_with_members( const exprt&, 
                                const value_sett&,
                                find_symbols_sett&);
bool contains_string_type(const exprt &expr);
bool contains_string_type(const typet &type);

void find_indexes(const exprt &src, std::set<exprt> &dest);

symbolt get_symbol(contextt &context, 
                   irep_idt &id, 
                   typet type);

#endif /*STRING_UTILS_H_*/
