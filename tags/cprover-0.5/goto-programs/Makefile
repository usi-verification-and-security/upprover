SRC = goto_convert.cpp goto_function.cpp goto_main.cpp goto_sideeffects.cpp \
      goto_program.cpp basic_blocks.cpp goto_threads.cpp goto_check.cpp \
      goto_function_pointers.cpp goto_functions.cpp goto_inline.cpp \
      remove_skip.cpp goto_convert_functions.cpp string_instrumentation.cpp \
      builtin_functions.cpp show_claims.cpp destructor.cpp set_claims.cpp \
      slicer.cpp invariant_set.cpp invariant_propagation.cpp \
      add_race_assertions.cpp rw_set.cpp read_goto_binary.cpp \
      invariant_set_domain.cpp static_analysis.cpp string_abstraction.cpp \
      goto_program_serialization.cpp goto_function_serialization.cpp \
      read_bin_goto_object.cpp goto_program_irep.cpp interpreter.cpp \
      interpreter_evaluate.cpp flow_insensitive_analysis.cpp \
      format_strings.cpp loop_numbers.cpp pointer_arithmetic.cpp \
      goto_program_template.cpp write_goto_binary.cpp remove_unreachable.cpp \
      remove_unused_functions.cpp dynamic_memory.cpp dump_c.cpp \
      wp.cpp goto_rw.cpp goto_clean_expr.cpp safety_checker.cpp \
      control_flow_graph.cpp depth_first_spanning_tree.cpp dominator_info.cpp \
      loops.cpp

OBJ = $(SRC:.cpp=.o)

INCLUDES= -I .. -I ../util

all: goto-programs.o

include ../config.inc
include ../common

###############################################################################

goto-programs.o: $(OBJ)
	$(LD) $(LDFLAGS) -o goto-programs.o $(OBJ)

test_wp: test_wp.o goto-programs.o
	$(CPLUS) $(LINKFLAGS) test_wp.o -o test_wp \
	../ansi-c/ansi-c.o  ../util/util.o  ../big-int/bigint.o goto-programs.o \
	../pointer-analysis/pointer-analysis.o ../langapi/langapi.o

clean:
	rm -f *.o

