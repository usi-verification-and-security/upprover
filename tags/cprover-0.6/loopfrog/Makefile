SRC = main.cpp \
      parseoptions.cpp \
      loop_summarizer.cpp \
      string_summarization.cpp \
      summary.cpp \
      string_utils.cpp \
      pointer_expr.cpp \
      value_set_duplication_adaptor.cpp \
      symex_assertion.cpp \
      replace_malloc.cpp \
      memstat.cpp \
      program_compression.cpp \
      conditional_goto_copy.cpp \
      invariant_propagation_adaptor.cpp \
      check_claims.cpp \
      local_slicer.cpp \
      localized_inlining.cpp \
      loopstore.cpp \
      leaping_goto_program.cpp \
      transform_loops.cpp \
      inlined_claims.cpp \
      summarization.cpp \
      value_set_alloc_adaptor.cpp \
      ../termination/replace_identifier.cpp \
      languages.cpp

OBJ = $(SRC:.cpp=.o) \
      invariants/invariants.o \
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

all: loopfrog

include ../config.inc
include ../common

ifdef MODULE_CPP
  OBJ += ../cpp/cpp.o
endif

ifdef MODULE_SPECC
  OBJ += ../specc/specc.o
endif

###############################################################################

.invariants:
	$(MAKE) $(MAKEARGS) -C invariants

loopfrog: .invariants $(OBJ)
	$(CPLUS) $(LINKFLAGS) -o loopfrog $(OBJ) $(LIBS)

clean:
	$(MAKE) $(MAKEARGS) -C invariants clean
	rm -f *.o loopfrog
