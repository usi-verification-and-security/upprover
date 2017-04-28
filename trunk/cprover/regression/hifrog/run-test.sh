#!/bin/bash

# Check the result $1 against the expected result $2
function check_result {
  cat $1 | diff - $2 > /dev/null
  RESULT="$?"
  if [[ ${RESULT} -gt 0 ]]; then
    echo ">>>> TEST FAILED"
    echo "<<<<<< PRODUCED RESULT"
    cat $1
    echo ">>>>>> EXPECTED RESULT"
    cat $2
    echo "----------------------" 
  fi
  return ${RESULT}
}

# Check a single file $1
function test_one {

  INPUT="$1"
  PREFIX=$PATH_reg${INPUT: : -2}
  FILE_PREFIX="${PREFIX}/${OUTPUT_DIR}_$2"
  SUMMARIES="${PREFIX}/__summaries_${OUTPUT_DIR}_$2"
  HIFROG_OUTPUT="${FILE_PREFIX}_hifrog_$IND.txt"
  HIFROG_RESULT="${FILE_PREFIX}_result.txt"
  HIFROG_TIME="${FILE_PREFIX}_time.txt"
  EXPECTED_OUTPUT="${INPUT}_out"
  IND=$((IND+1))

  if [[ ! -r ${INPUT} ]] ; then
    error "The input file ${INPUT} does not exist or it is not readable."
  fi
  if [[ ! -r ${EXPECTED_OUTPUT} ]] ; then
    warning "Test ignored due to missing file ${EXPECTED_OUTPUT} with expected result."
    ((IGNORED++))
    return 1
  fi
  
  #fixed so can pass params that are numbers
  p3="${3%\"}"
  p3="${p3#\"}"
 
  p4="${4%\"}"
  p4="${p4#\"}"
  
  p5="${5%\"}"
  p5="${p5#\"}"
  
  p6="${6%\"}"
  p6="${p6#\"}"
  
  p7="${7%\"}"
  p7="${p7#\"}"

  p8="${8%\"}"
  p8="${p8#\"}"

  p9="${9%\"}"
  p9="${p9#\"}"
  #stupid way to do it, but it works. If needed add more params
  echo ">> Run test case: $hifrog $PATH_reg$1 --logic $2 --save-summaries ${SUMMARIES}" $p3 $p4 $p5 $p6 $p7 $p8 $p9
  $hifrog $PATH_reg$1 --logic $2 --save-summaries ${SUMMARIES} $p3 $p4 $p5 $p6 $p7 $p8 $p9 >> ${HIFROG_OUTPUT} 2>&1
  if [[ $? -gt 0 ]]; then
    echo "HiFrog analysis failed (see ${HIFROG_OUTPUT})"
  fi

  # Filter the relevant information
  cat ${HIFROG_OUTPUT} | ${FILTER_RESULT} > ${HIFROG_RESULT}
  cat ${HIFROG_OUTPUT} | ${FILTER_TIME} > ${HIFROG_TIME}

  # Check the result against the expected one
  check_result ${HIFROG_RESULT} ${EXPECTED_OUTPUT}
}


################### MAIN ###############################
PATH_reg=$(readlink -f $0)
PATH_reg=${PATH_reg: : -11}
echo "This is the script for running regression tests"
echo " - date: $(date '+%Y-%m-%d at %H:%M.%S')"
echo " - host name $(hostname -f)"
echo " - script path: $(readlink -f $0)"
echo " - path regression tests: $PATH_reg"

FILTER_RESULT="./filter-result.sh"
FILTER_TIME="./filter-time.sh"
OUTPUT_DIR="output"
IND=1

# If works with absolute paths (when copying sub-folders of the regression and running somewhere)
# then please also state your absolute path of hifrog. If you are running it from the original
# location, you may ignore this comment
hifrog=./../../src/funfrog/hifrog 


# Iterating over all the test cases - When result shall match the known results
for filename in testcases/*.c_tc 
do
    # Per file, run all its inner test cases. 0 => clear summaries
    isFirst=1
    IFS=$'\n'
    for next in `cat $filename`
    do
        temp="${next%\"}"
	temp="${temp#\"}"
	arr=(`echo $temp | sed 's/,/\n/g'`)
        if (($isFirst==1))
        then
	  	isFirst=0
	    	# Prepare the environment
		rm -r ${arr[0]: : -2}
		mkdir "${arr[0]: : -2}"
        fi
	test_one ${arr[0]} ${arr[1]} ${arr[2]} ${arr[3]} ${arr[4]} ${arr[5]} ${arr[6]} ${arr[7]} ${arr[8]} ${arr[9]}
    done
done


