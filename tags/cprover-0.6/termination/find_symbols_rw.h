/*******************************************************************\

Module: 

Author: CM Wintersteiger

\*******************************************************************/

#ifndef CPROVER_SATABS_TERMINATION_FIND_SYMBOLS_RW_H_
#define CPROVER_SATABS_TERMINATION_FIND_SYMBOLS_RW_H_

#include <find_symbols.h>

void find_symbols_w(
  const exprt& lhs, 
  find_symbols_sett &l);

void find_symbols_w(
  const exprt& lhs, 
  std::set<exprt> &l);

void find_symbols_rw(
  const exprt& expr, 
  find_symbols_sett &l, 
  find_symbols_sett &r);

void find_symbols_rw(
  const exprt& lhs, 
  const exprt& rhs,
  find_symbols_sett &l, 
  find_symbols_sett &r);

bool is_subset( // true if l is a subset of r
  const find_symbols_sett &l,
  const find_symbols_sett &r);    

#endif
