/*******************************************************************\

Module: Abstractor Selection

Authors: Daniel Kroening, kroening@kroening.com

Date: September 2005

\*******************************************************************/

#include "select_abstractor.h"
#include "abstractor_wp.h"
#include "abstractor_satqe.h"
#include "abstractor_prover.h"

/*******************************************************************\

Function: select_abstractor

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

abstractort *select_abstractor(
  const cmdlinet &cmdline,
  const loop_componentt::argst &args)
{
  std::string name=
    cmdline.isset("abstractor")?cmdline.getval("abstractor"):"wp";

  if(name=="wp")
    return new abstractor_wpt(args);
  else if(name=="prover")
    #ifdef HAVE_PROVER
    return new abstractor_provert(args);
    #else
    throw "support for prover not linked in";
    #endif
  else if(name=="satqe")
    #ifdef HAVE_SATQE
    return new abstractor_satqet(args);
    #else
    throw "support for satqe not linked in";
    #endif
  else
    throw "unknown abstractor: "+name;
}
