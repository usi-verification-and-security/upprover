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
    "> ./diff goto-src goto-upg [call-tree]" << std::endl << std::endl <<
    "where (*) goto-s are the binaries to be compared;" << std::endl <<
    "      (*) call-tree is the file contained the storage of" << std::endl <<
    "          substituting scenario. changed function calls are to be marked there." << std::endl <<
    "          only std::cout if not specified." <<
    std::endl << std::endl;
}

void read(const char* file, goto_functionst& goto_functions) {

  stream_message_handlert mh(std::cout);
  contextt context;
  if(read_goto_binary(file, context, goto_functions, mh))
  {
    std::cerr << "Error reading file " << file << ".\n";
    return;
  }
}

int main(int argc, const char** argv) {

  fine_timet before, after;
  if (argc < 3 || argc > 4){
    print_help();
    return 1;
  }

  goto_functionst goto_functions_1;
  goto_functionst goto_functions_2;

  before=current_time();

  read(argv[1], goto_functions_1);
  read(argv[2], goto_functions_2);

  after=current_time();
  std::cout << "    LOAD Binaries Time: " << time2string(after-before) << " sec.\n";

  // Analyze both files

  difft diff(goto_functions_1, goto_functions_2);

  if (argc == 4){
    diff.set_output(argv[4]);
  }

  before=current_time();

  diff.do_diff();

  after=current_time();
  std::cout << "    PROCESSING Time: " << time2string(after-before) << " sec.\n";

}
