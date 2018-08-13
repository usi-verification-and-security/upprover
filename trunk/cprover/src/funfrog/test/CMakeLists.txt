include(FetchContent)

FetchContent_Declare(
    googletest
    GIT_REPOSITORY https://github.com/google/googletest.git
    GIT_TAG release-1.8.0
)

FetchContent_GetProperties(googletest)
if(NOT googletest_POPULATED)
    message("Fetching googletest")
    FetchContent_Populate(googletest)
    message("Finished fetching googletest")
  add_subdirectory(${googletest_SOURCE_DIR} ${googletest_BINARY_DIR})
endif()

add_subdirectory(unit)

