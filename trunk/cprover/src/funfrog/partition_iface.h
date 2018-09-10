/*******************************************************************

 Module: Keeps information about symbols on the boundary of a single
 partition (i.e., a block of SSA statements corresponding to a single
 function and its subtree).

\*******************************************************************/

#ifndef CPROVER_PARTITION_IFACE_H
#define	CPROVER_PARTITION_IFACE_H

#include "partition_fwd.h"

#include <util/type.h>
#include <util/symbol.h>
#include <util/std_expr.h>
#include <list>
#include <funfrog/interface/FlaRef.h>

class call_tree_nodet;

class partition_ifacet {
public:

  partition_ifacet(call_tree_nodet& _summary_info, partition_idt _parent_id, unsigned _call_loc);

  // Represented function
  irep_idt function_id;
  // Represented function node in substitution scenario
  call_tree_nodet& call_tree_node;
  
  // Filled during function call processing
  // TODO: Deprecate it! Split into iface vars and in_arg_symbols
  std::vector<symbol_exprt> argument_symbols;
  std::vector<symbol_exprt> in_arg_symbols;
  std::vector<symbol_exprt> out_arg_symbols;
  symbol_exprt retval_symbol;
  //symbol_exprt retval_tmp;
  symbol_exprt callstart_symbol;
  symbol_exprt callend_symbol;
  symbol_exprt error_symbol;
  bool assertion_in_subtree;
  bool returns_value;
  
  // Filled during conversion
  FlaRef callstart_literal;
  FlaRef callend_literal;
  FlaRef error_literal;
  
  // Connection with the corresponding partition
  partition_idt partition_id;
  partition_idt parent_id;
  
  // SSA Location of the call
  unsigned call_loc;

  std::vector<unsigned> A_vars;
  std::vector<unsigned> B_vars;
  std::vector<unsigned> AB_vars;

  std::vector<symbol_exprt> get_iface_symbols() const;

};

#endif	/* CPROVER_PARTITION_IFACE_H */

