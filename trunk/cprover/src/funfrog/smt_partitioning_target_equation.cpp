/*******************************************************************
 Module: Symex target equation which tracks different partitions for
 different deferred functions. Based on symex_target_equation.cpp.

 Author: Ondrej Sery

 \*******************************************************************/

#include <util/std_expr.h>

#include "smt_partitioning_target_equation.h"

#include "solvers/smtcheck_opensmt2.h"
#include "solvers/smt_itp.h"
#include "partition_iface.h"
#include "utils/naming_helpers.h"
#include "summary_store.h"

//#define DEBUG_ITP_SMT // ITP of SMT - testing
//#define DEBUG_ENCODING

#ifdef DISABLE_OPTIMIZATIONS
#include <fstream>
using namespace std;

#include "expr_pretty_print.h"
#endif


