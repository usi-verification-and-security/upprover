/*******************************************************************\

Module: simulator Selection

Authors: Daniel Kroening, kroening@kroening.com
         Karen Yorav

Date: June 2003

\*******************************************************************/

#include "select_simulator.h"
#include "simulator_symex.h"
#include "simulator_loop_detection.h"

/*******************************************************************\

Function: select_simulator

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

simulatort *select_simulator(
  const cmdlinet &cmdline,
  const loop_componentt::argst &args,
  contextt &_shadow_context)
{
  std::string name=
    cmdline.isset("simulator")?cmdline.getval("simulator"):"sat";
    
  bool path_slicing=
    !cmdline.isset("no-path-slicing");

  bool shortest_prefix=
    cmdline.isset("shortest-prefix");

  if(name=="sat")
  {
    if(cmdline.isset("loop-detection"))
      return new simulator_loop_detectiont(args, _shadow_context,
                                           path_slicing, shortest_prefix);

    return new simulator_symext(args, path_slicing, shortest_prefix);
  }
  else
    throw "unknown simulator: "+name;
}
