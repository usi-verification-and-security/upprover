#!/bin/bash

OUTPUT_DIR="output_tmp"
FILTER_RESULT="./filter-result.sh"

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


# Prepare etalon result for a single file $1
function process_one {

  INPUT="$1"
  INPUT_FILE="`basename ${INPUT}`"
  INPUT_DIR="`dirname ${INPUT}`"
  PREFIX="${INPUT_DIR}/${OUTPUT_DIR}/${INPUT_FILE}_"
  COMPILED="${PREFIX}a.out"
  GOTO_CC_OUTPUT="${PREFIX}goto-cc.txt"
  SUMMARIES="${PREFIX}__summaries"
  FUNFROG_OUTPUT="${PREFIX}funfrog.txt"
  FUNFROG_RESULT="${PREFIX}result.txt"
  EXPECTED_OUTPUT="${INPUT}_out"
  IGNORE_MARKER="${INPUT}_ignore"
  FUNFROG_PARAMS_FILE="${INPUT}_args"
  FUNFROG_PARAMS=""

  if [[ -e ${IGNORE_MARKER} ]]; then
    warning "File ignored, remove ${IGNORE_MARKER} to force etalon generation."
    return 0;
  fi

  info "Processing file: ${INPUT}"

  if [[ ! -r ${INPUT} ]] ; then
    error "The input file ${INPUT} does not exist or it is not readable."
  fi
  if [[ -r ${EXPECTED_OUTPUT} ]] ; then
    error "Etalon already exists ${EXPECTED_OUTPUT}, remove it to force generation."
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

  # Create the etalon
  mv ${FUNFROG_RESULT} ${EXPECTED_OUTPUT}
  if [[ $? -gt 0 ]]; then
    error "Failed to write the etalon file."
  fi

  # Check that the file is not empty
  if [[ ! -s ${EXPECTED_OUTPUT} ]]; then
    warning "The etalon file is empty. Check the ${EXPECTED_OUTPUT} file manually."
  fi

  # Clean the mess
  rm -f ${PREFIX}*

  echo "<<<<<< PRODUCED ETALON"
  cat ${EXPECTED_OUTPUT}
  echo "----------------------"
}

# We process only a single file (in order to discourage mass etalon changes)
if [[ ! -r $1 ]]; then
  # Test just the single given file
  error "Test file not found"
fi

process_one $1

info "Done"
