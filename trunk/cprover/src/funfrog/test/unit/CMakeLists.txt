include(GoogleTest)

add_executable(UtilsTest)
target_sources(UtilsTest
    PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/test_StringUtils.cpp"
    PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/test_ContainersUtils.cpp"
    PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/test_UnionFind.cpp"
    )

add_executable(PropSummariesTest)
target_sources(PropSummariesTest
    PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/test_PropSummaries.cpp"
    )

add_executable(SummaryStoreTest)
target_sources(SummaryStoreTest
    PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/test_SummaryStore.cpp"
    )
add_executable(SolversTest)
target_sources(SolversTest
    PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/test_Unsupported.cpp"
    )

set_target_properties(
    SolversTest
    UtilsTest
    PropSummariesTest
    SummaryStoreTest
    gtest
    gtest_main
    gmock
    gmock_main
    PROPERTIES
    CXX_STANDARD 11
    CXX_STANDARD_REQUIRED true
    )

target_link_libraries(UtilsTest gtest gtest_main)
target_include_directories(UtilsTest PRIVATE ${PROJECT_SOURCE_DIR}/funfrog)

target_link_libraries(PropSummariesTest hifrog-lib gtest gtest_main)

target_link_libraries(SummaryStoreTest hifrog-lib gtest gtest_main)

target_link_libraries(SolversTest hifrog-lib gtest gtest_main)

gtest_add_tests(TARGET UtilsTest
    )

gtest_add_tests(TARGET PropSummariesTest)

gtest_add_tests(TARGET SummaryStoreTest)

gtest_add_tests(TARGET SolversTest)
