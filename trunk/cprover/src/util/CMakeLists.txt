file(GLOB_RECURSE sources "*.cpp" "*.h")

# based on https://cmake.org/pipermail/cmake/2010-July/038015.html
file(WRITE ${CMAKE_BINARY_DIR}/version.cmake
  "
  file(STRINGS \${PROJECT_SOURCE_DIR}/config.inc
    config_inc_v REGEX \"CBMC_VERSION *= *[0-9\.]+\")
  string(REGEX REPLACE \"^CBMC_VERSION *= *\" \"\" CBMC_RELEASE \${config_inc_v})
  set(GIT_INFO \"n/a\")
  configure_file(\${CUR}/version.cpp.in version.cpp)
  "
)

file(WRITE ${CMAKE_CURRENT_BINARY_DIR}/version.cpp.in
  "const char *CBMC_VERSION=\"@CBMC_RELEASE@ (@GIT_INFO@)\";\n")
add_custom_target(
  generate_version_cpp
  BYPRODUCTS version.cpp
  COMMAND ${CMAKE_COMMAND}
    -D PROJECT_SOURCE_DIR=${PROJECT_SOURCE_DIR}
    -D CUR=${CMAKE_CURRENT_BINARY_DIR}
    -P ${CMAKE_BINARY_DIR}/version.cmake
)

add_library(util
  ${sources}
  version.cpp)

add_dependencies(util generate_version_cpp)

generic_includes(util)

target_link_libraries(util big-int langapi)
