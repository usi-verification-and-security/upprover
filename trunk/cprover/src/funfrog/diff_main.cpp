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

void do_it(const char* file1, const char* file2, const char* file3) {

  fine_timet before, after;
  stream_message_handlert mh(std::cout);

  goto_functionst goto_functions_1;
  goto_functionst goto_functions_2;

  // Load file 1

  contextt context_1;
  std::cout << "#1: Loading " << file1 << " ...\n";
  before=current_time();
  if(read_goto_binary(file1, context_1, goto_functions_1, mh))
  {
    std::cerr << "Error reading file " << file1 << ".\n";
    return;
  }
  after=current_time();
  std::cout << "    LOAD Time: " << time2string(after-before) << " sec.\n";

  // Load file 2

  contextt context_2;
  std::cout << "#2: Loading " << file2 << "' ...\n";
  before=current_time();
  if(read_goto_binary(file2, context_2, goto_functions_2, mh))
  {
    std::cerr << "Error reading file " << file2 << ".\n";
    return;
  }
  after=current_time();
  std::cout << "    LOAD Time: " << time2string(after-before) << " sec.\n";

  // Analyze both files

  before=current_time();

  difft().do_diff(goto_functions_1, goto_functions_2, file3);

  after=current_time();
  std::cout << "    PROCESSING Time: " << time2string(after-before) << " sec.\n";
}

int main(int argc, const char** argv) {

  if (argc < 3 || argc > 4){
    print_help();
    return 1;
  } else if (argc == 4){
    do_it(argv[1], argv[2], argv[3]);
  } else {
    do_it(argv[1], argv[2], "");
  }

}
