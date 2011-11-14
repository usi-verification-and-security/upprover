/*******************************************************************

 Module: Keeps information about symbols on the boundary of a single
 partition (i.e., a block of SSA statements corresponding to a single
 function and its subtree).

 Author: Ondrej Sery

\*******************************************************************/

#ifndef CPROVER_PARTITION_IFACE_H
#define	CPROVER_PARTITION_IFACE_H

#include <list>
#include <type.h>
#include <symbol.h>

#include "summary_info.h"
#include "partition.h"
#include "expr_pretty_print.h"

class partition_ifacet {
public:

  partition_ifacet(summary_infot& _summary_info, partition_idt _parent_id) : 
          function_id(_summary_info.get_function_id()),
          summary_info(_summary_info),
          callstart_symbol(ID_nil, typet(ID_bool)),
          callend_symbol(ID_nil, typet(ID_bool)),
          error_symbol(ID_nil, typet(ID_bool)),
          assertion_in_subtree(_summary_info.has_assertion_in_subtree()),
          returns_value(false),
          partition_id(partitiont::NO_PARTITION),
          parent_id(_parent_id)
  {}

  // Represented function
  irep_idt function_id;
  // Represented function node in substitution scenario
  summary_infot& summary_info;
  
  // Filled during function call processing
  // TODO: Deprecate it! Split into iface vars and in_arg_symbols
  std::vector<symbol_exprt> argument_symbols;
  std::vector<symbol_exprt> in_arg_symbols;
  std::vector<symbol_exprt> out_arg_symbols;
  symbol_exprt retval_symbol;
  symbol_exprt retval_tmp;
  symbol_exprt callstart_symbol;
  symbol_exprt callend_symbol;
  symbol_exprt error_symbol;
  bool assertion_in_subtree;
  bool returns_value;
  
  // Filled during conversion
  literalt callstart_literal;
  literalt callend_literal;
  literalt error_literal;
  
  // Connection with the corresponding partition
  partition_idt partition_id;
  partition_idt parent_id;
  
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
};

typedef std::list<partition_ifacet*> partition_iface_ptrst;
typedef std::vector<std::pair<partition_ifacet*, summary_idt> > interpolant_mapt;

#endif	/* CPROVER_PARTITION_IFACE_H */

