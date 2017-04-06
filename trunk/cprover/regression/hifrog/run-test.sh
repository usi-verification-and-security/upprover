#!/bin/bash
echo "This is the script for running regression tests"
echo " - date: $(date '+%Y-%m-%d at %H:%M.%S')"
echo " - host name $(hostname -f)"
echo " - script path: $(readlink -f $0)"

hifrog=./../../src/funfrog/hifrog
OUTPUT_DIR="output_tmp"

# Iterating over all the test cases - When result shall match the known results
for filename in testcases/*.c_tc 
do
    # Per file, run all its inner test cases. 0 => clear summaries
    echo "Run test cases file: $filename" 
    IFS=$'\n'
    for next in `cat $filename`
    do
	chrlen=${#next}
	if (($chrlen == 1))
	then
		echo "rm __summaries"
      		rm __summaries
	else
		echo $hifrog $next
                temp="${next%\"}"
		temp="${temp#\"}"
		arr=(`echo $temp | sed 's/,/\n/g'`)
		$hifrog ${arr[0]} --logic ${arr[1]} ${arr[2]} ${arr[3]} ${arr[4]} #stupid way to do it, but works
   	fi
    done
done

