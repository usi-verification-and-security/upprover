#!/bin/bash

if [[ $# != 4 ]]; then
    echo "Usage: $0 <tmpdir> --old <old1> [<old2> [...]]                "
    echo "                   --new <new1> [<new2> [...]]                "
    echo "where                                                         "
    echo "   <tmpdir>          is the directory for solving temproary files"
    echo "   <old1> ... <oldn> are the files of the old version"
    echo "                  containing the base version                 "
    echo "   <v1>           same for the upgraded version               "
    echo "   <filen>        the names of the c files (same for both     "
    echo "                  versions)                                   "
    exit 1
fi

example=$1; shift
v0=$1; shift
v1=$1; shift
name=$1; shift

cd $example
rm result/__* results/a.out

rm __*
echo "################################################################################"

#python ../naive-hybrid-check.py --initial-check tcas_v0/init_ass.txt tcas_v0 result tcas.c
python ../naive-hybrid-check-2.py --initial-check ${v0}/init_ass.txt ${v0} result ${name}
if [[ $? != 0 ]]; then exit; fi
cp result/a.out __old_a.out


echo "################################################################################"

#python ../naive-hybrid-check.py --upgrade-check __old_a.out __trusted tcas_v0/new_ass.txt tcas_v0 result tcas.c
python ../naive-hybrid-check-2.py --upgrade-check __old_a.out __trusted ${v1}/new_ass.txt ${v1} result ${name}


