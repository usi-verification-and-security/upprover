SRC = main.cpp \
      parseoptions.cpp \
      loop_classifier.cpp \
      string_utils.cpp \
      class_base.cpp \
      class_string.cpp \
      class_charsearch.cpp \
      class_nocharsearch.cpp \
      instr_string.cpp \
      instr_charsearch.cpp \
      instr_nocharsearch.cpp

OBJ = $(SRC:.cpp=.o) \
      ../ansi-c/ansi-c.o \
      ../big-int/bigint.o \
      ../langapi/csp_dummy.o \
      ../goto-programs/goto-programs.o \
      ../goto-symex/goto-symex.o \
      ../pointer-analysis/pointer-analysis.o \
      ../langapi/intrep_dummy.o \
      ../langapi/langapi.o \
      ../propdec/propdec.o \
      ../propsolve/propsolve.o \
      ../langapi/pvs_dummy.o \
      ../langapi/smvlang_dummy.o \
      ../langapi/promela_dummy.o \
      ../util/util.o \
      ../langapi/verilog_dummy.o \
      ../langapi/vhdl_dummy.o \
      ../langapi/smtlang_dummy.o \
      ../langapi/xmllang_dummy.o \
      ../langapi/netlist_dummy.o \
      ../langapi/pascal_dummy.o \
      ../langapi/bplang_dummy.o \
      ../langapi/simplifylang_dummy.o \
      ../langapi/csharp_dummy.o \
      ../langapi/cvclang_dummy.o \
      ../langapi/nsf_dummy.o \
      ../langapi/dp_dummy.o

INCLUDES= -I ../$(CHAFF) -I .. -I ../util

LIBS =

all: loopfrog

include ../config.inc
include ../common

ifdef MODULE_CPP
  OBJ += ../cpp/cpp.o
else
  OBJ += ../langapi/cpp_dummy.o
endif

ifdef MODULE_SPECC
  OBJ += ../specc/specc.o
else
  OBJ += ../langapi/specc_dummy.o
endif

ifdef MODULE_PHP
  OBJ += ../php/php.o
else
  OBJ += ../langapi/php_dummy.o
endif

###############################################################################

loopfrog: $(OBJ)
	$(CPLUS) $(LINKFLAGS) -o loopfrog $(OBJ) $(LIBS)

clean:
	rm -f *.o loopfrog
