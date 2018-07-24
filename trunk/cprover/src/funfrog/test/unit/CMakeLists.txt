include(GoogleTest)
add_executable(UnionFindTest)
target_sources(UnionFindTest 
    PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/test_UnionFind.cpp"
    )

add_executable(StringUtilsTest)
target_sources(StringUtilsTest
    PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/test_StringUtils.cpp"
    )

set_target_properties(
    UnionFindTest
    StringUtilsTest
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

target_link_libraries(StringUtilsTest gtest gtest_main)
target_include_directories(StringUtilsTest PRIVATE ${PROJECT_SOURCE_DIR}/funfrog)


#gtest_add_tests(TARGET UnionFindTest
#    TEST_LIST unionfindtests)

gtest_add_tests(TARGET UnionFindTest
    )

gtest_add_tests(TARGET StringUtilsTest
    )

#message("Discovered tests: " ${unionfindtests})
