file(GLOB_RECURSE sources "*.cpp" "*.h")
add_library(goto-programs ${sources})

generic_includes(goto-programs)

target_link_libraries(goto-programs java_bytecode util assembler langapi analyses ansi-c)
