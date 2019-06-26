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

  partition_ifacet(call_tree_nodet& _call_info, partition_idt _parent_id, unsigned _call_loc);

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
  
  
  //newly added for upgrade check
  
  symbol_exprt retval_tmp;
  void share_symbols(const partition_ifacet& other) {
    argument_symbols = other.argument_symbols;
    in_arg_symbols = other.in_arg_symbols;
    out_arg_symbols = other.out_arg_symbols;
    retval_symbol = other.retval_symbol;
    retval_tmp = other.retval_tmp;
    callstart_symbol = other.callstart_symbol;
    callend_symbol = other.callend_symbol;
    error_symbol = other.error_symbol;
    returns_value = other.returns_value;
    call_loc = other.call_loc;

#   if 0
    std::cerr << " === Sharing symbols:" << std::endl;
    std::cerr << " = Argument symbols:" << std::endl;
    {
      const std::vector<symbol_exprt>& symbols = argument_symbols;
      for (std::vector<symbol_exprt>::const_iterator it = symbols.begin();
              it != symbols.end(); ++it) {
        expr_pretty_print(std::cerr, *it);
      }
      std::cerr << std::endl;
    }
    std::cerr << " = Input argument symbols:" << std::endl;
    {
      const std::vector<symbol_exprt>& symbols = in_arg_symbols;
      for (std::vector<symbol_exprt>::const_iterator it = symbols.begin();
              it != symbols.end(); ++it) {
        expr_pretty_print(std::cerr, *it);
      }
      std::cerr << std::endl;
    }
    std::cerr << " = Output argument symbols:" << std::endl;
    {
      const std::vector<symbol_exprt>& symbols = out_arg_symbols;
      for (std::vector<symbol_exprt>::const_iterator it = symbols.begin();
              it != symbols.end(); ++it) {
        expr_pretty_print(std::cerr, *it);
      }
      std::cerr << std::endl;
    }
    expr_pretty_print(std::cerr << "Ret val: ", retval_symbol);
    expr_pretty_print(std::cerr << "Ret tmp: ", retval_tmp);
    expr_pretty_print(std::cerr << "Callstart: ", callstart_symbol);
    expr_pretty_print(std::cerr << "Callend: ", callend_symbol);
    expr_pretty_print(std::cerr << "Error: ", error_symbol);
#   endif
  }
  //
};

#endif	/* CPROVER_PARTITION_IFACE_H */

