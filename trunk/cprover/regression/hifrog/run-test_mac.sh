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
  INPUT_NO_EXT=${INPUT%%.c*}
  PREFIX=$PATH_reg$OUTDIR/$INPUT_NO_EXT
  FILE_PREFIX="${PREFIX}/${OUTPUT_PREFIX}_$2"
  SUMMARIES="${PREFIX}/__summaries_${OUTPUT_PREFIX}_$2"
  HIFROG_OUTPUT="${FILE_PREFIX}_hifrog_$IND.txt"
  HIFROG_RESULT="${FILE_PREFIX}_result.txt"
  HIFROG_TIME="${FILE_PREFIX}_time.txt"
  EXPECTED_OUTPUT="${INPUT}_out"
  EXPECTED_OUTPUT_CUF="${FILE_PREFIX}_cuf_expected_res.txt"
  IND=$((IND+1))

  if [[ ! -r ${INPUT} ]] ; then
    echo "The input file ${INPUT} does not exist or it is not readable."
  fi
  if [[ ! -r ${EXPECTED_OUTPUT} ]] ; then
    echo "Test ignored due to missing file ${EXPECTED_OUTPUT} with expected result."
    ((IGNORED++))
    return 1
  fi
  
  # $p3 is where is the expected output	
  if (("${#3}" > 1))
  then
    p3="${3%\"}"
    p3="${p3#\"}" 
    EXPECTED_OUTPUT=$p3
  fi

  #fixed so can pass params that are numbers 
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

  p10="${10%\"}"
  p10="${p10#\"}"

  p11="${11%\"}"
  p11="${p11#\"}"

  p12="${12%\"}"
  p12="${p12#\"}"

  p13="${13%\"}"
  p13="${p13#\"}"

  p14="${14%\"}"
  p14="${p14#\"}"

  p15="${15%\"}"
  p15="${p15#\"}"

  p16="${16%\"}"
  p16="${p16#\"}"

  #stupid way to do it, but it works. If needed add more params
  echo ">> Run test case: $hifrog "$1" --logic "$2" --save-summaries ${SUMMARIES} $p4 $p5 $p6 $p7 $p8 $p9 $p10 $p11 $p12 $p13 $p14 $p15"
  $hifrog "$1" --logic "$2" --save-summaries ${SUMMARIES} "$p4" "$p5" "$p6" "$p7" "$p8" "$p9" "$p10" "$p11" "$p12" "$p13" "$p14" "$p15" "$p16" >> ${HIFROG_OUTPUT} 2>&1
  if [[ $? -gt 0 ]]; then
    echo "HiFrog analysis failed (see ${HIFROG_OUTPUT})"
    echo "Verify output against: $EXPECTED_OUTPUT"
  fi

  # patch for cuf till it will support full functionality of hifrog (as other theories)
  if [ "$2" == "$QFCUF" ]
  then
    # Filter the relevant information
    cat ${HIFROG_OUTPUT} | ${FILTER_RESULT_CUF} > ${HIFROG_RESULT}
    cat ${HIFROG_OUTPUT} | ${FILTER_TIME} > ${HIFROG_TIME}
    cat ${EXPECTED_OUTPUT} | ${FILTER_RESULT_CUF} > ${EXPECTED_OUTPUT_CUF}
   
    # Check the result against the expected one
    check_result ${HIFROG_RESULT} ${EXPECTED_OUTPUT_CUF} 
  else
    # Filter the relevant information
    cat ${HIFROG_OUTPUT} | ${FILTER_RESULT} > ${HIFROG_RESULT}
    cat ${HIFROG_OUTPUT} | ${FILTER_TIME} > ${HIFROG_TIME}
   
    # Check the result against the expected one
    check_result ${HIFROG_RESULT} ${EXPECTED_OUTPUT} 
  fi
}


################### MAIN ###############################
PATH_reg=$(readlink $0)
PATH_reg=${PATH_reg: : -11}
echo "This is the script for running regression tests;supports: prop,qflra,qfuf,qfcuf."
echo " - date: $(date '+%Y-%m-%d at %H:%M.%S')"
echo " - host name $(hostname -f)"
echo " - script path: $(readlink $0)"
echo " - path regression tests: $PATH_reg"

FILTER_RESULT="./filter-result.sh"
FILTER_RESULT_CUF="./filter-result-cuf.sh"
FILTER_TIME="./filter-time.sh"
OUTPUT_PREFIX="output"
IND=1
QFCUF="qfcuf"

#Prepare main output folder
OUTDIR="mainReg_$OUTPUT_PREFIX"
rm -r $OUTDIR
mkdir $OUTDIR
echo " - create dir for output data of the regression tests: $OUTDIR"

# If works with absolute paths (when copying sub-folders of the regression and running somewhere)
# then please also state your absolute path of hifrog. If you are running it from the original
# location, you may ignore this comment
hifrog=./../../build/hifrog



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
		mkdir -p "$OUTDIR/${arr[1]: : -2}" 
                echo "***** Create Directory for test-case ${arr[1]} *****" 
        fi
	test_one ${arr[1]} ${arr[2]} ${arr[0]} ${arr[3]} ${arr[4]} ${arr[5]} ${arr[6]} ${arr[7]} ${arr[8]} ${arr[9]} ${arr[10]} ${arr[11]} ${arr[12]} ${arr[13]} ${arr[14]} ${arr[15]} ${arr[16]}
    done
done


