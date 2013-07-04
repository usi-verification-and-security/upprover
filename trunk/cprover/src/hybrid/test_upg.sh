#!/bin/bash

if [[ $# != 4 ]]; then
    echo "Usage: $0 <example-base> <v0> <v1> <name>                     "
    echo "where                                                         "
    echo "   <example-base> is the base directory of the things to check"
    echo "   <v0>           is the directory relative to <example-base> "
    echo "                  containing the base version                 "
    echo "   <v1>           same for the upgraded version               "
    echo "   <name>         the name of the c file (same for both       "
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
python ../naive-hybrid-check.py --initial-check ${v0}/CBMC_assertions_entryPoints_v0.txt ${v0} result ${name}
#python ../naive-hybrid-check.py --initial-check ${v0}/init_ass.txt ${v0} result ${name}
cp result/a.out __old_a.out


echo "################################################################################"

#python ../naive-hybrid-check.py --upgrade-check __old_a.out __trusted tcas_v0/new_ass.txt tcas_v0 result tcas.c
python ../naive-hybrid-check.py --upgrade-check __old_a.out __trusted ${v1}/CBMC_assertions_entryPoints_v1.txt ${v1} result ${name}
#python ../naive-hybrid-check.py --upgrade-check __old_a.out __trusted ${v1}/new_ass.txt ${v1} result ${name}

