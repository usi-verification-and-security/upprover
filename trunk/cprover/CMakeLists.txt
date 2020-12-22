cmake_minimum_required(VERSION 3.3)

# Default is release
if(NOT CMAKE_BUILD_TYPE)
set(CMAKE_BUILD_TYPE Release CACHE STRING "Choose the type of build, options are: None Debug Release RelWithDebInfo MinSizeRel." FORCE)
endif()

find_program(CCACHE_PROGRAM ccache)
if(CCACHE_PROGRAM)
    set_property(GLOBAL PROPERTY RULE_LAUNCH_COMPILE "${CCACHE_PROGRAM}")
    message(STATUS "Rule launch compile: ${CCACHE_PROGRAM}")
 endif()

set(CMAKE_EXPORT_COMPILE_COMMANDS true)

set(CMAKE_OSX_DEPLOYMENT_TARGET 10.9)

include(GNUInstallDirs)

set(CMAKE_ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib)
set(CMAKE_LIBRARY_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib)
set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin)

if("${CMAKE_CXX_COMPILER_ID}" STREQUAL "Clang" OR
   "${CMAKE_CXX_COMPILER_ID}" STREQUAL "AppleClang" OR
   "${CMAKE_CXX_COMPILER_ID}" STREQUAL "GNU"
)
    #   Ensure NDEBUG is not set for release builds
    set(CMAKE_CXX_FLAGS_RELEASE "-O2")
    set(CMAKE_CXX_FLAGS_RELWITHDEBINFO "-O2 -g")
    #   Enable lots of warnings
    set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wall -Wpedantic -Werror -Wno-deprecated-declarations")
elseif("${CMAKE_CXX_COMPILER_ID}" STREQUAL "MSVC")
    #   This would be the place to enable warnings for Windows builds, although
    #   config.inc doesn't seem to do that currently
endif()

set(enable_cbmc_tests off CACHE BOOL "Whether CBMC tests should be enabled")

set(sat_impl "minisat2" CACHE STRING
    "This setting controls the SAT library which is used. Valid values are 'minisat2' and 'glucose'"
)

if(${enable_cbmc_tests})
    enable_testing()
endif()

function(cprover_default_properties)
    set(CBMC_CXX_STANDARD 11)
    set(CBMC_CXX_STANDARD_REQUIRED true)
    set(CBMC_XCODE_ATTRIBUTE_CODE_SIGN_IDENTITY
            "Developer ID Application: Daniel Kroening")

    set_target_properties(
      ${ARGN}
     PROPERTIES
     CXX_STANDARD ${CBMC_CXX_STANDARD}
     CXX_STANDARD_REQUIRED ${CBMC_CXX_STANDARD_REQUIRED}
     XCODE_ATTRIBUTE_CODE_SIGN_IDENTITY ${CBMC_XCODE_ATTRIBUTE_CODE_SIGN_IDENTITY})
endfunction()

option(WITH_MEMORY_ANALYZER OFF
  "build the memory analyzer")

if(CMAKE_SYSTEM_NAME STREQUAL Linux)
set(WITH_MEMORY_ANALYZER_DEFAULT ON)
else()
set(WITH_MEMORY_ANALYZER_DEFAULT OFF)
endif()

option(WITH_MEMORY_ANALYZER ${WITH_MEMORY_ANALYZER_DEFAULT}
  "build the memory analyzer")

#HiFrog test
if(enable_hifrog_tests)
    enable_testing()
endif(enable_hifrog_tests)

add_subdirectory(src)
#add_subdirectory(regression)
#add_subdirectory(unit)

#add_subdirectory(jbmc)

cprover_default_properties(
    analyses
    ansi-c
    assembler
    big-int
    cbmc
    cbmc-lib
    cpp
    #driver
    goto-analyzer
    goto-analyzer-lib
    goto-cc
    goto-cc-lib
    goto-checker
	#goto-diff
    #goto-diff-lib
    goto-instrument
    goto-instrument-lib
    goto-programs
    goto-symex
    jsil
    json
	json-symtab-language
    langapi
    linking
    pointer-analysis
    solvers
    statement-list
	symtab2gb
	#testing-utils
	#unit
	util
	xml
    #miniz
	#miniBDD
	#mmcc
)
