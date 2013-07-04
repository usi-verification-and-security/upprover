#!/usr/bin/env python
import sys
import os
import naive_hybrid_check_2
import shutil

checker="/u1/home/aehyvari/src/funfrog/trunk/cprover/src/hybrid/naive-hybrid-check-2.py"

if __name__ == '__main__':
    if len(sys.argv) != 6:
        print("Usage: %s <example> <old> <new> <name> <yes|no> " % sys.argv[0])
        print
        print("where                                                         ")
        print("   <example>      is the directory containing the example     ")
        print("   <old>          is the dir which contains the old version   ")
        print("                  version and assertions                      ")
        print("   <new>          is the directory containing the new version ")
        print("                  and its assertions                          ")
        print("   <name>         the name of the c file (same for both       ")
        print("                  versions)                                   ")
        print("   <yes|no>       yes if use cbmc, no if use evolcheck        ")
        sys.exit(1)

    example = sys.argv[1]
    v0 = sys.argv[2]
    v1 = sys.argv[3]
    name = sys.argv[4]
    cbmc = sys.argv[5]

    if cbmc == "yes":
        use_cbmc = True
    else:
        use_cbmc = False

    os.chdir(example)
    shutil.rmtree("result")
    os.makedirs("result")
    map(lambda y: os.remove(y), filter(lambda x: x.startswith("__"), os.listdir(".")))

    print("################################################################################")
    naive_hybrid_check_2.init_check(os.path.join(v0, "init_ass.txt"), v0, "result", use_cbmc, [name])

    shutil.copy(os.path.join("result", "a.out"), "__old_a.out")
    print("################################################################################")
    naive_hybrid_check_2.upgr_check("__old_a.out", "__trusted", os.path.join(v1, "new_ass.txt"), v1, "result", use_cbmc, [name])

