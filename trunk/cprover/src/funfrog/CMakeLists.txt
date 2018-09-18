set(HIFROG_SOURCE_FILES
        nopartition/prepare_formula_no_partition.cpp
        nopartition/prepare_formula_no_partition.h
        nopartition/hifrog_symex_target_equation_no_partition.cpp
        nopartition/hifrog_symex_target_equation_no_partition.h
        nopartition/symex_no_partition.cpp
        nopartition/symex_no_partition.h
        assertion_info.h
        call_stack.h
        check_claims.cpp
        check_claims.h
        conversion_utils.h
        conversion_utils.cpp
        dependency_checker.cpp
        dependency_checker.h
        error_trace.cpp
        error_trace.h
        expr_pretty_print.cpp
        expr_pretty_print.h
        languages.cpp
        parseoptions.cpp
        parseoptions.h
        partition.h
        partition_iface.h
        partition_iface.cpp
        partitioning_slice.cpp
        partitioning_slice.h
        partitioning_target_equation.cpp
        partitioning_target_equation.h
        prop_summary_store.cpp
        prop_summary_store.h
        refiner_assertion_sum.cpp
        refiner_assertion_sum.h
        prepare_formula.cpp
        prepare_formula.h
        smt_summary_store.cpp
        smt_summary_store.h
        subst_scenario.cpp
        subst_scenario.h
        core_checker.cpp
        core_checker.h
        summary_info.cpp
        summary_info.h
        summary_store.cpp
        summary_store.h
        symex_assertion_sum.cpp
        symex_assertion_sum.h
        theory_refiner.cpp
        theory_refiner.h
        UserDefinedSummary.cpp
        UserDefinedSummary.h
        unwind.h
        version.h
        xml_interface.cpp
        xml_interface.h
        summary_store_fwd.h
        solvers/itp_fwd.h
        utils/ssa_helpers.h
        partition_fwd.h
        solvers/interpolating_solver_fwd.h
        interface/solver/solver.h
        interface/solver/interpolating_solver.h
        interface/convertor.h 
    )

################# TESTING #############################################
option(enable_hifrog_tests "Build the tests" OFF)
if(enable_hifrog_tests)
    if(CMAKE_VERSION VERSION_LESS 3.11)
        MESSAGE(WARNING "Minimum CMAKE version for building tests is 3.11")
    else(CMAKE_VERSION VERSION_LESS 3.11)
        enable_testing()
        add_subdirectory(${CMAKE_CURRENT_SOURCE_DIR}/test)
    endif(CMAKE_VERSION VERSION_LESS 3.11)
endif()
#########################################################################


option(PRODUCE_PROOF "" ON)
option(USE_Z3 "" OFF)

set(CMAKE_MODULE_PATH ${CMAKE_MODULE_PATH} "${PROJECT_SOURCE_DIR}/../cmake_modules/")

find_package(GMP REQUIRED)

add_library(hifrog-lib ${HIFROG_SOURCE_FILES})

add_executable(hifrog main.cpp
)

target_include_directories(hifrog-lib PUBLIC ${PROJECT_SOURCE_DIR})

target_compile_options(hifrog-lib PRIVATE -Wall)

if(PRODUCE_PROOF)
    #message("Compiling with PRODUCE_PROOF")
    target_compile_definitions(hifrog-lib PUBLIC -DPRODUCE_PROOF)
endif(PRODUCE_PROOF)

target_compile_definitions(hifrog-lib PUBLIC
    #-DDEBUG_PARTITIONING
    #-DDEBUG_SSA
    #-DDEBUG_SSA_SMT_CALL
    #-DDEBUG_GLOBALS
    #-DDISABLE_OPTIMIZATIONS
    #-DLATTICE_REF_ALGORITHM
    )

find_library(OPENSMT2_LIB NAMES opensmt2 libopensm2)
if(NOT OPENSMT2_LIB)
	message(FATAL_ERROR "opensmt library not found")
endif()

find_path(OPENSMT2_INCLUDE opensmt/opensmt2.h)
if(NOT OPENSMT2_INCLUDE)
	message(FATAL_ERROR "opensmt header files not found")
endif()

# Locating Z3 and setting related options
if(USE_Z3)
    find_package(Z3 CONFIG)
    if(Z3_FOUND)
        message("Z3 found!")
        message("Z3 version: ${Z3_VERSION_STRING}")
        message(${Z3_LIBRARIES})
        message(${Z3_CXX_INCLUDE_DIRS})

        target_compile_definitions(hifrog-lib PUBLIC -DZ3_AVAILABLE)
        target_include_directories(hifrog-lib PUBLIC ${Z3_CXX_INCLUDE_DIR})
        target_link_libraries(hifrog-lib ${Z3_LIBRARIES})
        target_sources(hifrog-lib PRIVATE
            ${CMAKE_CURRENT_SOURCE_DIR}/smt_z3_summary_store.cpp
            ${CMAKE_CURRENT_SOURCE_DIR}/smt_z3_summary_store.h
            ${CMAKE_CURRENT_SOURCE_DIR}/utils/unsupported_operations_z3.h
            ${CMAKE_CURRENT_SOURCE_DIR}/utils/unsupported_operations_z3.cpp
            )
    else(Z3_FOUND)
        message(FATAL ERROR "Unable to locate Z3 on your system! Specify the location or disable Z3 by setting USE_Z3 option to OFF")
    endif(Z3_FOUND)
endif(USE_Z3)
######## end of Z3 related section

add_subdirectory(solvers)
add_subdirectory(utils)

target_include_directories(hifrog-lib SYSTEM PUBLIC ${OPENSMT2_INCLUDE})
target_link_libraries(hifrog-lib ${OPENSMT2_LIB} ${GMP_LIBRARIES} ${GMPXX_LIBRARIES}
    )

target_link_libraries(hifrog-lib hifrog-utils ansi-c cpp goto-symex pointer-analysis solvers util xml
)

target_link_libraries(hifrog hifrog-lib)

set_target_properties(hifrog hifrog-lib hifrog-utils
PROPERTIES
RUNTIME_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}"
CXX_STANDARD 11
CXX_STANDARD_REQUIRED true
)
