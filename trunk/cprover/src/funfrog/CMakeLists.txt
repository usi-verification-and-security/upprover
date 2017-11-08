set(HIFROG_SOURCE_FILES
        nopartition/smt_assertion_no_partition.cpp
        nopartition/smt_assertion_no_partition.h
        nopartition/smt_symex_target_equation.cpp
        nopartition/smt_symex_target_equation.h
        nopartition/symex_no_partition.cpp
        nopartition/symex_no_partition.h
        solvers/check_opensmt2.h
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
        function_info.cpp
        function_info.h
        hifrog.cpp
        hifrog.h
        languages.cpp
        main.cpp
        parseoptions.cpp
        parseoptions.h
        partition.h
        partition_iface.h
        partitioning_slice.cpp
        partitioning_slice.h
        partitioning_target_equation.cpp
        partitioning_target_equation.h
        prop_assertion_sum.cpp
        prop_assertion_sum.h
        prop_dependency_checker.cpp
        prop_dependency_checker.h
        prop_partitioning_target_equation.cpp
        prop_partitioning_target_equation.h
        prop_refiner_assertion_sum.cpp
        prop_refiner_assertion_sum.h
        prop_summary_store.cpp
        prop_summary_store.h
        refiner_assertion_sum.cpp
        refiner_assertion_sum.h
        smt_assertion_sum.cpp
        smt_assertion_sum.h
        smt_dependency_checker.cpp
        smt_dependency_checker.h
        smt_partitioning_target_equation.cpp
        smt_partitioning_target_equation.h
        smt_refiner_assertion_sum.cpp
        smt_refiner_assertion_sum.h
        smt_summary_store.cpp
        smt_summary_store.h
        subst_scenario.cpp
        subst_scenario.h
        summarization_context.h
        summarizing_checker.cpp
        summarizing_checker.h
        summary_info.cpp
        summary_info.h
        summary_store.cpp
        summary_store.h
        #sumo.cpp
        symex_assertion_sum.cpp
        symex_assertion_sum.h
        theory_refiner.cpp
        theory_refiner.h
        unwind.h
        version.h
        xml_interface.cpp
        xml_interface.h
    utils/naming_helpers.h utils/naming_helpers.cpp partition_iface_fwd.h summary_store_fwd.h summarization_context_fwd.h utils/coloring_mode.h solvers/itp_fwd.h)

set(CMAKE_MODULE_PATH ${CMAKE_MODULE_PATH} "${CMAKE_SOURCE_DIR}/../cmake_modules/")

find_package(GMP REQUIRED)

add_executable(hifrog ${HIFROG_SOURCE_FILES} $<TARGET_OBJECTS:cprover>)

target_compile_options(hifrog PRIVATE  -Wall)

target_compile_definitions(hifrog PUBLIC -DPRODUCE_PROOF)

target_compile_definitions(hifrog PRIVATE
    #-DDEBUG_PARTITIONING
    #-DDEBUG_SSA
    #-DDEBUG_SSA_SMT_CALL
    #-DDEBUG_GLOBALS
    )

target_link_libraries(hifrog -lopensmt2 ${GMP_LIBRARIES} ${GMPXX_LIBRARIES})

message(${CMAKE_BINARY_DIR})

set_target_properties(hifrog
PROPERTIES
RUNTIME_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}"
)
