SRC = 	goto-cc.cpp \
        cmdline_options.cpp get_base_name.cpp \
        gcc_cmdline.cpp ms_cl_cmdline.cpp \
        compile.cpp \
        languages.cpp \
        xml_binaries/xml_irep_hashing.cpp \
        xml_binaries/xml_symbol_hashing.cpp \
        xml_binaries/xml_symbol.cpp \
        xml_binaries/xml_goto_function.cpp \
        xml_binaries/xml_goto_function_hashing.cpp \
        xml_binaries/xml_goto_program.cpp \
        xml_binaries/xml_goto_program_hashing.cpp \
        xml_binaries/read_goto_object.cpp

OBJ = $(SRC:.cpp=.o) \
      ../big-int/bigint.o \
      ../goto-programs/goto-programs.o \
      ../pointer-analysis/pointer-analysis.o \
      ../util/util.o \
      ../ansi-c/ansi-c.o \
      ../xmllang/xmllang.o \
      ../langapi/langapi.o

INCLUDES= -I .. -I ../util

LIBS =

all: goto-cc

include ../config.inc
include ../common

ifdef MODULE_CPP
  OBJ += ../cpp/cpp.o
  CPLUSFLAGS += -D HAVE_CPP
endif

###############################################################################

goto-cc: $(OBJ)
	$(CPLUS) $(LINKFLAGS) -o goto-cc $(OBJ) $(LIBS) 

clean:
	rm -f $(SRC:.cpp=.o) $(SRC:.cpp=.d) goto-cc
