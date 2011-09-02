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

class partition_ifacet {
public:

  partition_ifacet(summary_infot& _summary_info, partition_idt _parent_id) : 
          function_id(_summary_info.get_function_id()),
          summary_info(_summary_info),
          callstart_symbol(typet(ID_bool)),
          callend_symbol(typet(ID_bool)),
          error_symbol(typet(ID_bool)),
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
};

typedef std::list<partition_ifacet*> partition_iface_ptrst;
typedef std::vector<std::pair<partition_ifacet*, summary_idt> > interpolant_mapt;

#endif	/* CPROVER_PARTITION_IFACE_H */

