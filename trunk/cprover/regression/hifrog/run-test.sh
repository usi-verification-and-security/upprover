#!/bin/bash
echo "This is the script for running regression tests"
echo " - date: $(date '+%Y-%m-%d at %H:%M.%S')"
echo " - host name $(hostname -f)"
echo " - script path: $(readlink -f $0)"

hifrog=../../cprover/src/funfrog/hifrog
OUTPUT_DIR="output_tmp"

