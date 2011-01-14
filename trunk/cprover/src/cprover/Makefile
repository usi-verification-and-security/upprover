SRC = cprover.cpp lang.cpp register_languages.cpp
OBJ = cprover.o   lang.o   register_languages.o \
      ../ansi-c/ansi-c.o \
      ../big-int/bigint.o \
      ../intrep/intrep.o \
      ../langapi/langapi.o \
      ../util/util.o \
      ../xmllang/xmllang.o \
      ../bplang/bplang.o

INCLUDES= -I ../$(CHAFF) -I .. -I ../util

LIBS =

all: cprover

include ../config.inc
include ../common

ifdef MODULE_CPP
  OBJ += ../cpp/cpp.o
  CPLUSFLAGS += -D HAVE_CPP
endif

ifdef MODULE_SPECC
  OBJ += ../specc/specc.o
  CPLUSFLAGS += -D HAVE_SPECC
endif

ifdef MODULE_VERILOG
  OBJ += ../verilog/verilog.o
  CPLUSFLAGS += -D HAVE_VERILOG
endif

ifdef MODULE_PHP
  OBJ += ../php/php.o
  CPLUSFLAGS += -D HAVE_PHP
endif

ifdef MODULE_SMTLANG
  OBJ += ../smtlang/smtlang.o
  CPLUSFLAGS += -D HAVE_SMTLANG
endif

ifdef MODULE_MDL
  OBJ += ../mdllang/mdllang.o
  CPLUSFLAGS += -D HAVE_MDL
endif

ifdef MODULE_SMV
  OBJ += ../smvlang/smvlang.o
  CPLUSFLAGS += -D HAVE_SMV
endif

###############################################################################

cprover: $(OBJ)
	$(CPLUS) $(LINKFLAGS) -o cprover $(OBJ) $(LIBS)

clean:
	rm -f $(OBJ) *.o cprover
