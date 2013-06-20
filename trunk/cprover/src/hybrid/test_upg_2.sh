#!/bin/bash

if [[ $# != 4 ]]; then
    echo "Usage: $0 <example> <old> <new> <name>                        "
    echo
    echo "where                                                         "
    echo "   <example>      is the directory containing the example     "
    echo "   <old>          is the dir which contains the old version   "
    echo "                  version and assertions                      "
    echo "   <new>          is the directory containing the new version "
    echo "                  and its assertions                          "
    echo "   <filen>        the name of the c file (same for both       "
    echo "                  versions)                                   "
    exit 1
fi

example=$1; shift
v0=$1; shift
v1=$1; shift
name=$1; shift

cwd=`pwd`
cd $example
rm result/__* results/a.out

rm __*
echo "################################################################################"

#python ../naive-hybrid-check.py --initial-check tcas_v0/init_ass.txt tcas_v0 result tcas.c
python ../naive-hybrid-check-2.py --initial-check ${cwd}/${v0}/init_ass.txt ${cwd}/${v0} result ${name}
if [[ $? != 0 ]]; then exit; fi
cp result/a.out __old_a.out


echo "################################################################################"

#python ../naive-hybrid-check.py --upgrade-check __old_a.out __trusted tcas_v0/new_ass.txt tcas_v0 result tcas.c
python ../naive-hybrid-check-2.py --upgrade-check __old_a.out __trusted ${cwd}/${v1}/new_ass.txt ${cwd}/${v1} result ${name}


