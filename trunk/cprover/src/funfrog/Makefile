SRC = main.cpp \
      summary_info.cpp \
      parseoptions.cpp \
      check_claims.cpp \
      symex_assertion_sum.cpp \
      summarizing_checker.cpp \
      inlined_claims.cpp \
      expr_pretty_print.cpp \
      partitioning_target_equation.cpp \
      interpolation/opensmt_solver.cpp

OBJ = $(SRC:.cpp=.o) \
      ../loopfrog/languages.o \
      ../loopfrog/memstat.o \
      ../loopfrog/value_set_alloc_adaptor.o \
      ../loopfrog/replace_malloc.o \
      ../big-int/bigint.o \
      ../goto-programs/goto-programs.o \
      ../goto-symex/goto-symex.o \
      ../pointer-analysis/pointer-analysis.o \
      ../solvers/solvers.o \
      ../util/util.o \
      ../langapi/langapi.o \
      ../ansi-c/ansi-c.o

INCLUDES= -I ../$(CHAFF) -I .. -I ../util

LIBS =

all: funfrog

include ../config.inc
include ../common

ifdef MODULE_CPP
  OBJ += ../cpp/cpp.o
endif

ifdef MODULE_SPECC
  OBJ += ../specc/specc.o
endif

###############################################################################

funfrog: $(OBJ)
	$(CPLUS) $(LINKFLAGS) -o funfrog $(OBJ) $(LIBS)

clean:
	rm -f *.o *.d funfrog
