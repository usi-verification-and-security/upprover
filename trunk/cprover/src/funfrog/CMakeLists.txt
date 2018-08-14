set(HIFROG_SOURCE_FILES
        nopartition/smt_assertion_no_partition.cpp
        nopartition/smt_assertion_no_partition.h
        nopartition/smt_symex_target_equation.cpp
        nopartition/smt_symex_target_equation.h
        nopartition/symex_no_partition.cpp
        nopartition/symex_no_partition.h
        solvers/check_opensmt2.h
        solvers/check_opensmt2.cpp
        solvers/interpolating_solver.h
        solvers/itp.h
        solvers/prop_itp.cpp
        solvers/prop_itp.h
        solvers/satcheck_opensmt2.cpp
        solvers/satcheck_opensmt2.h
        solvers/smt_itp.cpp
        solvers/smt_itp.h
        solvers/smtcheck_opensmt2.cpp
        solvers/smtcheck_opensmt2.h
        solvers/smtcheck_opensmt2_cuf.cpp
        solvers/smtcheck_opensmt2_cuf.h
        solvers/smtcheck_opensmt2_lra.cpp
        solvers/smtcheck_opensmt2_lra.h
        solvers/smtcheck_opensmt2_uf.cpp
        solvers/smtcheck_opensmt2_uf.h
        solvers/naming_boolbv.h
        assertion_info.h
        assertion_sum.h
        call_stack.h
        check_claims.cpp
        check_claims.h
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
        partitioning_slice.cpp
        partitioning_slice.h
        partitioning_target_equation.cpp
        partitioning_target_equation.h
        prop_dependency_checker.cpp
        prop_dependency_checker.h
        prop_summary_store.cpp
        prop_summary_store.h
        refiner_assertion_sum.cpp
        refiner_assertion_sum.h
        prepare_formula.cpp
        prepare_formula.h
        smt_dependency_checker.cpp
        smt_dependency_checker.h
        smt_partitioning_target_equation.cpp
        smt_partitioning_target_equation.h
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
        #sumo.cpp
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
        utils/naming_helpers.h
        utils/naming_helpers.cpp
        summary_store_fwd.h
        solvers/itp_fwd.h
        utils/ssa_helpers.h
        partition_fwd.h
        solvers/interpolating_solver_fwd.h
        #reportt.cpp reportt.h
        utils/UnionFind.cpp
        utils/UnionFind.h
        utils/string_utils.h)

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

set(CMAKE_MODULE_PATH ${CMAKE_MODULE_PATH} "${PROJECT_SOURCE_DIR}/../cmake_modules/")

find_package(GMP REQUIRED)

add_library(hifrog-lib ${HIFROG_SOURCE_FILES})

add_executable(hifrog main.cpp
)

target_include_directories(hifrog-lib PUBLIC ${PROJECT_SOURCE_DIR})

target_compile_options(hifrog-lib PUBLIC  -Wall)

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
    )

find_library(OPENSMT2_LIB NAMES opensmt2 libopensm2)
if(NOT OPENSMT2_LIB)
	message(FATAL_ERROR "opensmt library not found")
endif()

find_path(OPENSMT2_INCLUDE opensmt/opensmt2.h)
if(NOT OPENSMT2_INCLUDE)
	message(FATAL_ERROR "opensmt header files not found")
endif()

target_include_directories(hifrog-lib SYSTEM PUBLIC ${OPENSMT2_INCLUDE})
target_link_libraries(hifrog-lib ${OPENSMT2_LIB} ${GMP_LIBRARIES} ${GMPXX_LIBRARIES}
    )

target_link_libraries(hifrog-lib
    ansi-c
    cbmc-lib #this is here only because of no_partition, if that is done in a different way, remove this dependency
    cpp
    goto-symex
    solvers
    util
    xml
)

target_link_libraries(hifrog hifrog-lib)

set_target_properties(hifrog hifrog-lib
PROPERTIES
RUNTIME_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}"
CXX_STANDARD 11
CXX_STANDARD_REQUIRED true
)
