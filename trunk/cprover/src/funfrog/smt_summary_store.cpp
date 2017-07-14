/*******************************************************************\

Module: Storage class for function summaries (union-find).

Author: Ondrej Sery

\*******************************************************************/

#include <string.h>
#include "solvers/smt_itp.h"
#include "smt_summary_store.h"

// Serialization SMT
void smt_summary_storet::serialize(std::ostream& out) const
{
  for (storet::const_iterator it = store.begin();
          it != store.end();
          ++it) {
    if (it->is_repr()) {      
      it->summary->serialize(out);
    }
  }
}

// SMT logics deser
void smt_summary_storet::deserialize(const std::string& in, smtcheck_opensmt2t *decider)
{
    repr_count = 0;

    if(!decider)
        return;

    store.clear();

    // KE: add support for many summary files for lattice refinement
    std::set<std::string> summary_files;
    get_files(summary_files, in);
    for(auto it = summary_files.begin(); it != summary_files.end() ; ++it)
    {
        if(decider->getMainSolver()->readFormulaFromFile(it->c_str()))
        {    
            vec<Tterm>& functions = decider->getLogic()->getFunctions();
            for(int i = 0; i < functions.size(); ++i)
            {
                summaryt *itp = new smt_summaryt();
                Tterm &tterm = functions[i];
                string fname = tterm.getName();
                string qless = smtcheck_opensmt2t::unquote_varname(fname);
                string idxless = smtcheck_opensmt2t::remove_index(qless);
                int midx = get_max_id(idxless);
                int fidx = smtcheck_opensmt2t::get_index(fname);
                assert(fidx >= 0);
                //assert(midx != fidx);
                int next_idx = midx + 1;
                ++max_ids[idxless];// = max(fidx, midx);
                //string fixed_name = smtcheck_opensmt2t::quote_varname(qless);
                string fixed_name = smtcheck_opensmt2t::insert_index(idxless, next_idx);
                tterm.setName(fixed_name);
                itp->setTterm(tterm);
                itp->setLogic(decider->getLogic());
                itp->setInterpolant(tterm.getBody());
                itp->set_valid(1);
                store.push_back(nodet(i, *itp));
                repr_count++;
            }

            max_id += repr_count; // KE: We add new summaries so we need to inc the max
        }
    }
    
    return;
}

/*******************************************************************\

Function: summary_storet::insert_summary

  Inputs:

 Outputs:

 Purpose: Inserts a new summary, the given summary is invalidated

\*******************************************************************/

summary_idt smt_summary_storet::insert_summary(summaryt& summary)
{
  summary_idt id = max_id++;
  summary.set_valid(1);

  Tterm *tterm = summary.getTterm();
  assert(tterm);
  string fname = tterm->getName();
  string qless = smtcheck_opensmt2t::unquote_varname(fname);
  string idxless = smtcheck_opensmt2t::remove_index(qless);
  int midx = get_max_id(idxless);
  int next_idx = midx + 1;
  max_ids[idxless] = next_idx;// = max(fidx, midx);
  string fixed_name = smtcheck_opensmt2t::insert_index(idxless, next_idx);
  tterm->setName(fixed_name);

  store.push_back(nodet(id, summary));
  repr_count++;
  return id;
}

/*
 Returns a list of summary files
 */
void get_files(std::set<std::string>& files, std::string set){

  int length=set.length();

  for(int idx=0; idx<length; idx++)
  {
    std::string::size_type next=set.find(",", idx);
    files.insert(set.substr(idx, next-idx));

    if(next==std::string::npos) break;
    idx=next;
  }
}