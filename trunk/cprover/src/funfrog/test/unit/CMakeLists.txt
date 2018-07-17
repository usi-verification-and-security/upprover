include(GoogleTest)
add_executable(UnionFindTest)
target_sources(UnionFindTest 
    PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/test_UnionFind.cpp"
    )

set_target_properties(
    UnionFindTest
    gtest
    gtest_main
    gmock
    gmock_main
    PROPERTIES
    CXX_STANDARD 11
    CXX_STANDARD_REQUIRED true
    )

target_link_libraries(UnionFindTest gtest gtest_main)
target_include_directories(UnionFindTest PRIVATE ${PROJECT_SOURCE_DIR}/funfrog)


gtest_add_tests(TARGET UnionFindTest
    TEST_LIST unionfindtests)

#message("Discovered tests: " ${unionfindtests})
