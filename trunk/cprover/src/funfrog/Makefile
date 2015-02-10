include ../config.inc

SHARED_SRC := \
      expr_pretty_print.cpp \
      function_info.cpp \
      summary_store.cpp \
      solvers/satcheck_periplo.cpp \
      solvers/prop_itp.cpp

FUNFROG_SRC := \
      diff.cpp \
      partitioning_target_equation.cpp \
      partitioning_slice.cpp \
      summary_info.cpp \
      subst_scenario.cpp \
      xml_interface.cpp \
      parseoptions.cpp \
      languages.cpp \
      check_claims.cpp \
      refiner_assertion_sum.cpp \
      prop_assertion_sum.cpp \
      dependency_checker.cpp \
      symex_assertion_sum.cpp \
      summarizing_checker.cpp \
      upgrade_checker.cpp \
      main.cpp

SUMO_SRC := \
      sumo.cpp

DIFF_SRC := \
      diff.cpp \
      diff_main.cpp

OBJ += \
      $(SHARED_SRC:.cpp=$(OBJEXT)) \
      ../ansi-c/ansi-c$(LIBEXT) \
      ../linking/linking$(LIBEXT) \
      ../big-int/big-int$(LIBEXT) \
      ../goto-programs/goto-programs$(LIBEXT) \
      ../pointer-analysis/value_set$(OBJEXT) \
      ../pointer-analysis/dereference$(OBJEXT) \
      ../pointer-analysis/add_failed_symbols$(OBJEXT) \
      ../pointer-analysis/rewrite_index$(OBJEXT) \
      ../pointer-analysis/goto_program_dereference$(OBJEXT) \
      ../langapi/langapi$(LIBEXT) \
      ../analyses/analyses$(LIBEXT) \
      ../assembler/assembler$(LIBEXT) \
      ../solvers/solvers$(LIBEXT) \
      ../util/util$(LIBEXT)


FUNFROG_OBJ := \
      $(FUNFROG_SRC:.cpp=$(OBJEXT)) \
      ../goto-symex/goto-symex$(LIBEXT) \
      ../xmllang/xmllang$(LIBEXT) \
      ../cbmc/symex_bmc$(OBJEXT) \
      ../cpp/cpp$(LIBEXT) \
      ../java_bytecode/java_bytecode$(LIBEXT) \
      $(OBJ)

SUMO_OBJ := \
      $(SUMO_SRC:.cpp=$(OBJEXT)) \
      $(OBJ)

DIFF_OBJ := \
      $(DIFF_SRC:.cpp=$(OBJEXT)) \
      ../ansi-c/ansi-c$(LIBEXT) \
      ../linking/linking$(LIBEXT) \
      ../big-int/big-int$(LIBEXT) \
      ../goto-programs/goto-programs$(LIBEXT) \
      ../pointer-analysis/value_set$(OBJEXT) \
      ../pointer-analysis/dereference$(OBJEXT) \
      ../pointer-analysis/add_failed_symbols$(OBJEXT) \
      ../pointer-analysis/rewrite_index$(OBJEXT) \
      ../pointer-analysis/goto_program_dereference$(OBJEXT) \
      ../langapi/langapi$(LIBEXT) \
      ../analyses/analyses$(LIBEXT) \
      ../assembler/assembler$(LIBEXT) \
      ../util/util$(LIBEXT)

SRC := ${FUNFROG_SRC} ${SUMO_SRC} ${DIFF_SRC}

include ../common

all: evolcheck$(EXEEXT) sumo$(EXEEXT)

PERIPLO_SRCDIR ?= /home/leonardo/devel/periplo

PERIPLO_INCLUDE ?= -I$(PERIPLO_SRCDIR)/src -I$(PERIPLO_SRCDIR)/src/minisat -I$(PERIPLO_SRCDIR)/src/minisat/mtl -I$(PERIPLO_SRCDIR)/src/minisat/core -I$(PERIPLO_SRCDIR)/src/minisat/utils/ -I$(PERIPLO_SRCDIR)/src/satsolvers -I$(PERIPLO_SRCDIR)/src/simplifiers -I$(PERIPLO_SRCDIR)/src/common -I$(PERIPLO_SRCDIR)/src/egraph -I$(PERIPLO_SRCDIR)/src/sorts -I$(PERIPLO_SRCDIR)/src/cnfizers -I$(PERIPLO_SRCDIR)/src/proof -I$(PERIPLO_SRCDIR)/src/api

INCLUDES := $(PERIPLO_INCLUDE) -I .. -I ../util

#LIBS := -L/home/loris/libs/lib
ifeq ($(origin PERIPLO_LIBDIR), undefined)
    LIBS := -L/usr/lib
else
    LIBS := -L$(PERIPLO_LIBDIR)
endif

GCCFLAGS += -DUSE_PERIPLO 

CP_CXXFLAGS += -DUSE_PERIPLO -DFULL_LABELING

ifneq ($(wildcard ../bv_refinement/Makefile),)
  OBJ += ../bv_refinement/bv_refinement$(LIBEXT)
  CP_CXXFLAGS += -DHAVE_BV_REFINEMENT
endif

ifneq ($(wildcard ../cpp/Makefile),)
  OBJ += ../cpp/cpp$(LIBEXT)
  CP_CXXFLAGS += -DHAVE_CPP
endif

ifneq ($(wildcard ../java_bytecode/Makefile),)
  OBJ += ../java_bytecode/java_bytecode$(LIBEXT)
  CP_CXXFLAGS += -DHAVE_JAVA_BYTECODE
endif

ifneq ($(wildcard ../specc/Makefile),)
  OBJ += ../specc/specc$(LIBEXT)
  CP_CXXFLAGS += -DHAVE_SPECC
endif

ifneq ($(wildcard ../php/Makefile),)
  OBJ += ../php/php$(LIBEXT)
  CP_CXXFLAGS += -DHAVE_PHP
endif

###############################################################################

evolcheck$(EXEEXT): $(FUNFROG_OBJ)
	$(LINKBIN) -static -lperiplolibrary -lgmpxx -lgmp  

funfrog$(EXEEXT): $(FUNFROG_OBJ)
	$(LINKBIN) -static -lperiplolibrary -lgmpxx -lgmp 

sumo$(EXEEXT): $(SUMO_OBJ)
	$(LINKBIN) -static -lperiplolibrary -lgmpxx -lgmp 

diff$(EXEEXT): $(DIFF_OBJ)
	$(LINKBIN) -static
	mv diff goto-diff

clean:
	rm -f *.o *.d funfrog evolcheck sumo diff __omega_* __calltree.xml
	rm -f solvers/*.o solvers/*.d

re: clean all
