#!/bin/bash

OUTPUT_DIR="output_tmp"
FILTER_RESULT="./filter-result.sh"
FILTER_TIME="./filter-time.sh"

PASSED=0
FAILED=0
IGNORED=0
TOTAL=0

RED="\e[1;31m"
GREEN="\e[1;32m"
YELLOW="\e[1;33m"
NO_COLOR="\e[0m"


# Print error
function info {
  echo -e ${GREEN}" * "${NO_COLOR}$1
}

# Print error
function error {
  echo -e ${RED}" * "${NO_COLOR}$1
  exit 1
}

# Print warning
function warning {
  echo -e ${YELLOW}" * "${NO_COLOR}$1
}


# Check the result $1 against the expected result $2
function check_result {
  cat $1 | diff - $2 > /dev/null
  RESULT="$?"
  
  if [[ $? -gt 0 ]]; then
    info "The test result differs from the expected result"
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
  INPUT_FILE="`basename ${INPUT}`"
  INPUT_DIR="`dirname ${INPUT}`"
  PREFIX="${INPUT_DIR}/${OUTPUT_DIR}/${INPUT_FILE}_"
  COMPILED="${PREFIX}a.out"
  GOTO_CC_OUTPUT="${PREFIX}goto-cc.txt"
  SUMMARIES="${PREFIX}__summaries"
  FUNFROG_OUTPUT="${PREFIX}funfrog.txt"
  FUNFROG_RESULT="${PREFIX}result.txt"
  FUNFROG_TIME="${PREFIX}time.txt"
  EXPECTED_OUTPUT="${INPUT}_out"
  IGNORE_MARKER="${INPUT}_ignore"
  FUNFROG_PARAMS_FILE="${INPUT}_args"
  FUNFROG_PARAMS=""

  if [[ -e ${IGNORE_MARKER} ]]; then
    return 0;
  fi

  info "Testing file: ${INPUT}"
  ((TOTAL++))

  if [[ ! -r ${INPUT} ]] ; then
    error "The input file ${INPUT} does not exist or it is not readable."
  fi
  if [[ ! -r ${EXPECTED_OUTPUT} ]] ; then
    warning "Test ignored due to missing file ${EXPECTED_OUTPUT} with expected result."
    ((IGNORED++))
    return 1
  fi

  # Prepare the environment
  if [[ ! -e "${INPUT_DIR}/${OUTPUT_DIR}" ]] ; then
    mkdir "${INPUT_DIR}/${OUTPUT_DIR}"
  fi
  rm -f ${PREFIX}*

  # Compilation with goto-cc
  goto-cc ${INPUT} -o ${COMPILED} >${GOTO_CC_OUTPUT} 2>&1
  if [[ $? -gt 0 ]] ; then
    error "Compilation failed (see ${GOTO_CC_OUTPUT})"
  else
    rm ${GOTO_CC_OUTPUT}
  fi

  # Additional test parameters?
  if [[ -r ${FUNFROG_PARAMS_FILE} ]]; then
    FUNFROG_PARAMS=`cat ${FUNFROG_PARAMS_FILE}`
    echo "   Additional funfrog parameters: ${FUNFROG_PARAMS}"
  fi

  # Analysis using funfrog
  funfrog ${FUNFROG_PARAMS} --save-summaries ${SUMMARIES} --load-summaries ${SUMMARIES} "${COMPILED}" > ${FUNFROG_OUTPUT} 2>&1
  if [[ $? -gt 0 ]]; then
    error "Funfrog analysis failed (see ${FUNFROG_OUTPUT})"
  fi

  # Filter the relevant information
  cat ${FUNFROG_OUTPUT} | ${FILTER_RESULT} > ${FUNFROG_RESULT}
  cat ${FUNFROG_OUTPUT} | ${FILTER_TIME} > ${FUNFROG_TIME}

  # Check the result against the expected one
  check_result ${FUNFROG_RESULT} ${EXPECTED_OUTPUT}
  if [[ $? -gt 0 ]]; then
    echo "   TEST FAILED"
    ((FAILED++))
  else
    echo "   TEST SUCCESSFUL"
    ((PASSED++))
    rm ${FUNFROG_OUTPUT}
    rm ${FUNFROG_RESULT}
  fi
}

# Run test on all [.c/.cpp/.C] files in the given directory $1
function test_dir {
  info "Testing files in directory: $1"

  for FILE in $1/*{c,cpp,C} ; do
    if [[ -r ${FILE} ]]; then
      test_one ${FILE}
    fi
  done
  for DIR in $1/* ; do
    if [[ -d ${DIR} ]]; then
      test_dir ${DIR}
    fi
  done
}

# Setup testing dir
if [[ -z $1 ]]; then
  # Test all files in all subdirectories
  info "Testing all files in all subdirectories"
  for x in * ; do
    if [[ -d $x ]] && [[ ! ${OUTPUT_DIR} == $x ]] && [[ ! ${OUTPUT_DIR} == ".*" ]] ; then
      test_dir $x
    fi
  done

elif [[ -d $1 ]]; then
  # Test all files in the given directory
  test_dir $1

elif [[ -r $1 ]]; then
  # Test just the single given file
  info "Single file selected for testing"
  test_one $1
fi

info "Done"
echo   "      Total tests:   ${TOTAL}"
echo   "      Passed tests:  ${PASSED}"
if [[ ${FAILED} -gt 0 ]]; then
  echo "      Failed tests:  ${FAILED}"
fi
if [[ ${IGNORED} -gt 0 ]]; then
  echo "      Ignored tests: ${IGNORED}"
fi

