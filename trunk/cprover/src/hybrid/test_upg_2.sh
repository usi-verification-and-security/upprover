#!/bin/bash
checker=/u1/home/aehyvari/src/funfrog/trunk/cprover/src/hybrid/naive-hybrid-check-2.py

if [[ $# != 5 ]]; then
    echo "Usage: $0 <example> <old> <new> <name> <yes|no>               "
    echo
    echo "where                                                         "
    echo "   <example>      is the directory containing the example     "
    echo "   <old>          is the dir which contains the old version   "
    echo "                  version and assertions                      "
    echo "   <new>          is the directory containing the new version "
    echo "                  and its assertions                          "
    echo "   <name>         the name of the c file (same for both       "
    echo "                  versions)                                   "
    echo "   <yes|no>       yes if use cbmc, no if use evolcheck        "
    exit 1
fi

example=$1; shift
v0=$1; shift
v1=$1; shift
name=$1; shift
cbmc=$1; shift

cd $example
rm result/__* results/a.out

rm __*
echo "################################################################################"

#python ../naive-hybrid-check.py --initial-check tcas_v0/init_ass.txt tcas_v0 result tcas.c
python ${checker} --initial-check ${v0}/init_ass.txt ${v0} result ${cbmc} ${name}
if [[ $? != 0 ]]; then exit; fi
cp result/a.out __old_a.out


echo "################################################################################"

#python ../naive-hybrid-check.py --upgrade-check __old_a.out __trusted tcas_v0/new_ass.txt tcas_v0 result tcas.c
python ${checker} --upgrade-check __old_a.out __trusted ${v1}/new_ass.txt ${v1} result ${cbmc} ${name}


