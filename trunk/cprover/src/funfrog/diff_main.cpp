/*******************************************************************

 Module: Diff utility for 2 goto-binaries. cmd wrapper

 Author: Grigory Fedyukovich

\*******************************************************************/

#include "diff.h"

void print_help() {
  std::cout <<
    "goto-diff by Grigory Fedyukovich (grigory.fedyukovich@usi.ch)" << std::endl <<
    std::endl <<
    "Expected usage:" << std::endl <<
    "> ./diff goto-src goto-upg [--output-locs]" << std::endl << std::endl <<
    "where (*) goto-s are the binaries to be compared;" << std::endl <<
//    "      (*) call-tree is the file contained the storage of" << std::endl <<
//    "          substituting scenario. changed function calls are to be marked there." << std::endl <<
//    "          only std::cout if not specified." <<
    "      (*) do output only locations of the modified instructions" << std::endl <<
    std::endl << std::endl;
}

void read(message_handlert& mh, const char* file, goto_functionst& goto_functions) {

  contextt context;
  if(read_goto_binary(file, context, goto_functions, mh))
  {
    std::cerr << "Error reading file " << file << ".\n";
    return;
  }
}

int main(int argc, const char** argv) {

  //fine_timet before, after;
  if (argc < 3 || argc > 4){
    print_help();
    return 1;
  }

  goto_functionst goto_functions_1;
  goto_functionst goto_functions_2;

  stream_message_handlert mh(std::cout);

  //before=current_time();

  read(mh, argv[1], goto_functions_1);
  read(mh, argv[2], goto_functions_2);

  //after=current_time();
  //std::cout << "    LOAD Binaries Time: " << time2string(after-before) << " sec.\n";

  // Analyze both files

  difft diff(mh, goto_functions_1, goto_functions_2);

  if (argc == 4){
    if (!strcmp(argv[3],"--output-locs")){
      diff.set_locs_output();
    }
  }

  //before=current_time();

  diff.do_diff();

  //after=current_time();
  //std::cout << "    PROCESSING Time: " << time2string(after-before) << " sec.\n";

}
