SRC = symex_target.cpp symex_target_equation.cpp basic_symex.cpp \
      symex_main.cpp goto_trace.cpp build_goto_trace.cpp \
      symex_function.cpp goto_symex_state.cpp symex_dereference.cpp \
      symex_goto.cpp builtin_functions.cpp slice.cpp symex_other.cpp \
      slice_by_trace.cpp xml_goto_trace.cpp symex_decl.cpp \
      precondition.cpp postcondition.cpp symex_clean_expr.cpp

OBJ = $(SRC:.cpp=.o)

INCLUDES= -I .. -I ../util

all: goto-symex.o

include ../config.inc
include ../common

###############################################################################

goto-symex.o: $(OBJ)
	$(LD) $(LDFLAGS) -o $@ $(OBJ)

clean:
	rm -f *.o

