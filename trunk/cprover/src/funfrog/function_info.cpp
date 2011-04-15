/*******************************************************************

 Module: Summarizing information associated with a single function,
 i.e., a set of discovered summaries and set of call sites.

 Author: Ondrej Sery

\*******************************************************************/

#include "function_info.h"
#include <fstream>

/*******************************************************************\

Function: function_infot::serialize

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void function_infot::serialize(std::ostream& out) const
{
  out << summaries.size() << std::endl;

  for (interpolantst::const_iterator it = summaries.begin();
          it != summaries.end();
          ++it) {

    it->serialize(out);
  }
}

/*******************************************************************\

Function: function_infot::deserialize

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void function_infot::deserialize(std::istream& in)
{
  unsigned nsummaries;

  in >> nsummaries;

  if (in.fail())
    return;

  summaries.clear();
  summaries.reserve(nsummaries);

  for (unsigned i = 0; i < nsummaries; ++i)
  {
    summaries.push_back(interpolantt());
    interpolantt& itp = summaries.back();

    itp.deserialize(in);
  }
}


/*******************************************************************\

Function: function_infot::serialize_infos

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void function_infot::serialize_infos(std::ostream& out, const function_infost& infos)
{
  unsigned nonempty_summaries = 0;

  for (function_infost::const_iterator it = infos.begin();
          it != infos.end();
          ++it) {
    if (it->second.get_summaries().size() > 0)
      ++nonempty_summaries;
  }
  
  out << nonempty_summaries << std::endl;

  for (function_infost::const_iterator it = infos.begin();
          it != infos.end();
          ++it) {

    if (it->second.get_summaries().size() == 0)
      continue;

    out << it->first << std::endl;
    it->second.serialize(out);
  }
}

/*******************************************************************\

Function: deserialize_infos

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void function_infot::deserialize_infos(std::istream& in, function_infost& infos)
{
  unsigned nfunctions;

  in >> nfunctions;

  if (in.fail())
    return;

  for (unsigned i = 0; i < nfunctions; ++i)
  {
    std::string f_name;
    in >> f_name;

    irep_idt f_id(f_name);
    function_infost::iterator it = infos.find(f_id);

    if (it == infos.end()) {
      function_infot tmp(f_id);

      tmp.deserialize(in);
      continue;
    }

    it->second.deserialize(in);
  }
}

/*******************************************************************\

Function: function_infot::serialize_infos

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void function_infot::serialize_infos(const std::string& file, const function_infost& infos)
{
  std::ofstream out;
  out.open(file.c_str());

  if (out.fail()) {
    std::cerr << "Failed to serialize the function summaries (file: " << file <<
            " cannot be accessed)" << std::endl;
    return;
  }

  serialize_infos(out, infos);

  if (out.fail()) {
    throw "Failed to serialize the function summaries.";
  }

  out.close();
}

/*******************************************************************\

Function: deserialize_infos

  Inputs:

 Outputs:

 Purpose:

\*******************************************************************/

void function_infot::deserialize_infos(const std::string& file, function_infost& infos)
{
  std::ifstream in;
  in.open(file.c_str());

  if (in.fail()) {
    std::cerr << "Failed to serialize function summaries (file: " << file <<
            " cannot be read)" << std::endl;
    return;
  }

  deserialize_infos(in, infos);

  if (in.fail()) {
    throw "Failed to load function summaries.";
  }

  in.close();
}

