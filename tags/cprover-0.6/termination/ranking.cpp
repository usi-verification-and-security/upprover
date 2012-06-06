/********************************************************************\

 Module: Ranking Function Synthesis

 Author: CM Wintersteiger

 Date: September 2008

\********************************************************************/

#include <memory>

#include "ranking_sat.h"
#include "ranking_qbf.h"
#include "ranking_qbf_complete.h"
#include "ranking_qbf_bitwise.h"
#include "ranking_rankfinder.h"
#include "ranking_seneschal.h"
#include "ranking_smt.h"

#include "ranking.h"

/*******************************************************************\

Function: ranking

  Inputs:

 Outputs:

 Purpose:

\********************************************************************/

exprt ranking(
  const std::string &mode,
  const bodyt &body,
  const contextt &context,
  contextt &shadow_context,
  message_handlert &mh,
  unsigned verbosity)
{
  if(mode=="" || mode=="sat")
  {
    ranking_synthesis_satt rank_synth(body, context, shadow_context, mh);
    rank_synth.set_verbosity(verbosity);
    return rank_synth.ranking();
  }
  else if(mode=="qbf")
  {
    ranking_synthesis_qbft rank_synth(body, context, shadow_context, mh, 
                            ranking_synthesis_qbft::COEFFICIENTS_UNCONSTRAINED);
    rank_synth.set_verbosity(verbosity);
    return rank_synth.ranking();
  }
  else if(mode=="qbfC")
  {
    ranking_synthesis_qbft rank_synth(body, context, shadow_context, mh, 
                            ranking_synthesis_qbft::COEFFICIENTS_CONSTRAINED);
    rank_synth.set_verbosity(verbosity);
    return rank_synth.ranking();
  }
  else if(mode.substr(0,4)=="qbfb")
  {
    ranking_synthesis_qbf_bitwiset rank_synth(body, context, shadow_context, mh);
    rank_synth.set_verbosity(verbosity);
    
    if(mode=="qbfbA")
      rank_synth.set_mode(ranking_synthesis_qbf_bitwiset::F_AFFINE);    
    else if(mode=="qbfbC")
      rank_synth.set_mode(ranking_synthesis_qbf_bitwiset::F_CONJUNCTIVE);
    else if(mode=="qbfbD")
      rank_synth.set_mode(ranking_synthesis_qbf_bitwiset::F_DISJUNCTIVE);
    else if(mode=="qbfbN")
      rank_synth.set_mode(ranking_synthesis_qbf_bitwiset::F_NOTHING);
    else if(mode=="qbfbP")
      rank_synth.set_mode(ranking_synthesis_qbf_bitwiset::F_PROJECTIONS);

    return rank_synth.ranking();
  }
  else if(mode=="qbfc")
  {
    ranking_synthesis_qbf_completet rank_synth(body, context, shadow_context, mh);
    rank_synth.set_verbosity(verbosity);
    return rank_synth.ranking();
  }
  else if(mode=="rf")
  {
    ranking_synthesis_rankfindert rank_synth(body, context, shadow_context, mh);
    rank_synth.set_verbosity(verbosity);
    return rank_synth.ranking();
  }
  else if(mode=="seneschal")
  {
    ranking_synthesis_seneschalt rank_synth(body, context, shadow_context, mh);
    rank_synth.set_verbosity(verbosity);
    return rank_synth.ranking();
  }
  else if(mode=="smt")
  {
    ranking_synthesis_smtt rank_synth(body, context, shadow_context, mh);
    rank_synth.set_verbosity(verbosity);
    return rank_synth.ranking();
  }
  else if(mode=="none")
  {
    return nil_exprt();
  }
  else
    throw "Unknown rank function synthesis mode `" + mode + "'";
}
