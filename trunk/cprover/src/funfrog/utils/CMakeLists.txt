add_library(hifrog-utils OBJECT)

target_link_libraries(hifrog-utils PUBLIC util)
target_include_directories(hifrog-utils PUBLIC ${PROJECT_SOURCE_DIR})

target_sources(hifrog-utils
    PRIVATE
        ${CMAKE_CURRENT_SOURCE_DIR}/naming_helpers.h
        ${CMAKE_CURRENT_SOURCE_DIR}/naming_helpers.cpp
        #${CMAKE_CURRENT_SOURCE_DIR}/UnionFind.cpp
        ${CMAKE_CURRENT_SOURCE_DIR}/UnionFind.h
        ${CMAKE_CURRENT_SOURCE_DIR}/string_utils.h
        ${CMAKE_CURRENT_SOURCE_DIR}/string_utils.cpp
        ${CMAKE_CURRENT_SOURCE_DIR}/containers_utils.h
        ${CMAKE_CURRENT_SOURCE_DIR}/expressions_utils.cpp
    )

target_sources(hifrog-lib
    PRIVATE
        ${CMAKE_CURRENT_SOURCE_DIR}/unsupported_operations.h
        ${CMAKE_CURRENT_SOURCE_DIR}/unsupported_operations.cpp
        ${CMAKE_CURRENT_SOURCE_DIR}/unsupported_operations_opensmt2.h
        ${CMAKE_CURRENT_SOURCE_DIR}/unsupported_operations_opensmt2.cpp
)
