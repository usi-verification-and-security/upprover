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

#include "partition.h"

class partition_ifacet {
public:

  partition_ifacet(irep_idt _function_id) : function_id(_function_id),
          callstart_symbol(typet(ID_bool)),
          callend_symbol(typet(ID_bool)),
          returns_value(false),
          partition_id(partitiont::NO_PARTITION)
  {}

  // Represented function
  irep_idt function_id;
  
  // Filled during function call processing
  // TODO: Deprecate it! Split into iface vars and in_arg_symbols
  std::vector<symbol_exprt> argument_symbols;
  std::vector<symbol_exprt> in_arg_symbols;
  std::vector<symbol_exprt> out_arg_symbols;
  symbol_exprt retval_symbol;
  symbol_exprt retval_tmp;
  symbol_exprt callstart_symbol;
  symbol_exprt callend_symbol;
  bool returns_value;
  
  // Filled during conversion
  literalt callstart_literal;
  literalt callend_literal;
  
  // Connection with the corresponding partition
  partition_idt partition_id;
};

typedef std::list<partition_ifacet*> partition_iface_ptrst;

#endif	/* CPROVER_PARTITION_IFACE_H */

