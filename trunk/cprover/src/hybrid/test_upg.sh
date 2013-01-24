#!/bin/bash

cd TCAS_hybrid_example
rm result/*
rm __*
echo "################################################################################"

python ../naive-hybrid-check.py --initial-check tcas_v0/init_ass.txt tcas_v0 result tcas.c

cp result/a.out __old_a.out


echo "################################################################################"

python ../naive-hybrid-check.py --upgrade-check __old_a.out __trusted tcas_v0/new_ass.txt tcas_v0 result tcas.c


