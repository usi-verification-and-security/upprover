/*******************************************************************\

Module: Custom bitvector-rankfunction typechecker

Author: CM Wintersteiger

Date: May 2009

\*******************************************************************/

#ifndef RANKFUNCTION_TYPECHECK_H_
#define RANKFUNCTION_TYPECHECK_H_

#include <typecheck.h>
#include <ansi-c/ansi_c_parse_tree.h>
#include <context.h>
#include <namespace.h>
#include <message.h>

bool parse_rank_function(const std::string &code, contextt &context,
                         const namespacet &ns, message_handlert &mh, exprt &rf);


class rankfunction_typecheckt:public typecheckt
{
public:
  rankfunction_typecheckt(
    ansi_c_parse_treet &_parse_tree,
    contextt &_context,
    const namespacet &_ns,
    message_handlert &_message_handler):
      typecheckt(_message_handler),
      parse_tree(_parse_tree),
      ns(_context),
      ext_ns(_ns)
  {
  }

  virtual ~rankfunction_typecheckt(void) { }

  virtual void typecheck(void)
  {
    throw ("N/A"); // This is only meant for expr's
  }

  virtual void typecheck_expr(exprt &expr);

protected:
  ansi_c_parse_treet &parse_tree;
  namespacet ns;
  namespacet ext_ns;
};


#endif /* RANKFUNCTION_TYPECHECK_H_ */
