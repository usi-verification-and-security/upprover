SHARED_SRC := \
      expr_pretty_print.cpp \
      function_info.cpp \
      solvers/satcheck_opensmt.cpp \
      solvers/prop_itp.cpp

FUNFROG_SRC := \
      partitioning_target_equation.cpp \
      partitioning_slice.cpp \
      summary_info.cpp \
      parseoptions.cpp \
      check_claims.cpp \
      refiner_assertion_sum.cpp \
      prop_assertion_sum.cpp \
      symex_assertion_sum.cpp \
      summarizing_checker.cpp \
      inlined_claims.cpp \
      main.cpp

SUMO_SRC := \
      sumo.cpp

SHARED_OBJ := \
      $(SHARED_SRC:.cpp=.o) \
      ../util/util.o \
      ../big-int/bigint.o \
      ../goto-programs/goto-programs.o \
      ../pointer-analysis/pointer-analysis.o \
      ../langapi/langapi.o \
      ../ansi-c/ansi-c.o \
      ../solvers/solvers.o

FUNFROG_OBJ := \
	    $(SHARED_OBJ) \
      $(FUNFROG_SRC:.cpp=.o) \
      ../loopfrog/languages.o \
      ../loopfrog/memstat.o \
      ../loopfrog/value_set_alloc_adaptor.o \
      ../loopfrog/replace_malloc.o \
      ../goto-symex/goto-symex.o \
      ../cbmc/symex_bmc.o

SUMO_OBJ := \
      $(SHARED_OBJ) \
      $(SUMO_SRC:.cpp=.o)

all: funfrog

include ../config.inc
include ../common

INCLUDES := $(OPENSMT_INCLUDE) -I ../$(CHAFF) -I .. -I ../util
LIBS := -L $(OPENSMT_LIBDIR) -lopensmt-1.0 -lgmpxx -lgmp

ifdef MODULE_CPP
  OBJ += ../cpp/cpp.o
endif

ifdef MODULE_SPECC
	OBJ += ../specc/specc.o
endif

###############################################################################

funfrog: $(FUNFROG_OBJ)
	$(CPLUS) $(LINKFLAGS) -o funfrog $(FUNFROG_OBJ) $(LIBS)

sumo: $(SUMO_OBJ)
	$(CPLUS) $(LINKFLAGS) -o sumo $(SUMO_OBJ) $(LIBS)

clean:
	rm -f *.o *.d funfrog sumo
	rm -f solvers/*.o solvers/*.d

re: clean all
