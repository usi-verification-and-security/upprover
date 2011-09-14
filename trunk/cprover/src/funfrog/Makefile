include ../config.inc
include ../common

SHARED_SRC := \
      expr_pretty_print.cpp \
      function_info.cpp \
      summary_store.cpp \
      solvers/satcheck_opensmt.cpp \
      solvers/prop_itp.cpp

FUNFROG_SRC := \
      partitioning_target_equation.cpp \
      partitioning_slice.cpp \
      summary_info.cpp \
      subst_scenario.cpp \
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

DIFF_SRC := \
      diff.cpp

SHARED_OBJ := \
      $(SHARED_SRC:.cpp=$(OBJEXT)) \
      ../util/util$(LIBEXT) \
      ../big-int/bigint$(OBJEXT) \
      ../goto-programs/goto-programs$(LIBEXT) \
      ../pointer-analysis/pointer-analysis$(LIBEXT) \
      ../langapi/langapi$(LIBEXT) \
      ../ansi-c/ansi-c$(LIBEXT) \
      ../solvers/solvers$(LIBEXT)

FUNFROG_OBJ := \
      $(FUNFROG_SRC:.cpp=$(OBJEXT)) \
      ../loopfrog/languages$(OBJEXT) \
      ../loopfrog/memstat$(OBJEXT) \
      ../loopfrog/value_set_alloc_adaptor$(OBJEXT) \
      ../loopfrog/replace_malloc$(OBJEXT) \
      ../goto-symex/goto-symex$(LIBEXT) \
      ../cbmc/symex_bmc$(OBJEXT) \
	    $(SHARED_OBJ)

SUMO_OBJ := \
      $(SUMO_SRC:.cpp=$(OBJEXT)) \
      $(SHARED_OBJ)

DIFF_OBJ := \
      $(DIFF_SRC:.cpp=$(OBJEXT)) \
      $(SHARED_OBJ)

all: funfrog$(EXEEXT) sumo$(EXEEXT)

INCLUDES := $(OPENSMT_INCLUDE) -I .. -I ../util
LIBS := -L $(OPENSMT_LIBDIR)

ifdef MODULE_BV_REFINEMENT
  FUNFROG_OBJ += ../bv_refinement/bv_refinement$(LIBEXT)
  CXXFLAGS += -DHAVE_BV_REFINEMENT
endif

ifdef MODULE_CPP
  FUNFROG_OBJ += ../cpp/cpp$(LIBEXT)
  CXXFLAGS += -DHAVE_CPP
endif

###############################################################################

funfrog$(EXEEXT): $(FUNFROG_OBJ)
	$(LINKBIN) $(FUNFROG_OBJ) -lopensmt-1.0 -lgmpxx -lgmp

sumo$(EXEEXT): $(SUMO_OBJ)
	$(LINKBIN) $(SUMO_OBJ) -lopensmt-1.0 -lgmpxx -lgmp

diff$(EXEEXT): $(DIFF_OBJ)
	$(LINKBIN) $(DIFF_OBJ)

clean:
	rm -f *.o *.d funfrog sumo diff
	rm -f solvers/*.o solvers/*.d

re: clean all
