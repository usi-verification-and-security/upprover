SRC = main.cpp parseoptions.cpp bmc.cpp dimacs.cpp languages.cpp \
      bv_cbmc.cpp symex_bmc.cpp show_vcc.cpp cbmc_solvers.cpp \
      xml_interface.cpp \
      counterexample_beautification.cpp \
      counterexample_beautification_greedy.cpp \
      counterexample_beautification_pbs.cpp
OBJ = $(SRC:.cpp=.o) \
      ../ansi-c/ansi-c.o \
      ../big-int/bigint.o \
      ../goto-programs/goto-programs.o \
      ../goto-symex/goto-symex.o \
      ../pointer-analysis/pointer-analysis.o \
      ../langapi/langapi.o \
      ../xmllang/xmllang.o \
      ../solvers/solvers.o \
      ../util/util.o

INCLUDES= -I .. -I ../util

LIBS =

all: cbmc

include ../config.inc
include ../common

ifdef MODULE_BV_REFINEMENT
  OBJ += ../bv_refinement/bv_refinement.o
  CPLUSFLAGS += -DHAVE_BV_REFINEMENT
endif

ifdef MODULE_CPP
  OBJ += ../cpp/cpp.o
  CPLUSFLAGS += -DHAVE_CPP
endif

ifdef MODULE_JAVA
  OBJ += ../java/java.o
  CPLUSFLAGS += -DHAVE_JAVA
endif

ifdef MODULE_SPECC
  OBJ += ../specc/specc.o
  CPLUSFLAGS += -DHAVE_SPECC
endif

ifdef MODULE_PHP
  OBJ += ../php/php.o
  CPLUSFLAGS += -DHAVE_PHP
endif

ifneq ($(Z3),)
  CPLUSFLAGS += -DHAVE_Z3
endif

ifneq ($(BOOLECTOR),)
  CPLUSFLAGS += -DHAVE_BOOLECTOR
endif

###############################################################################

cbmc: $(OBJ)
	$(CPLUS) $(LINKFLAGS) -o cbmc $(OBJ) $(LIBS)

clean:
	rm -f *.o cbmc
