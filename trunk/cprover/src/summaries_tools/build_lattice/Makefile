include ../../config.inc
-include local

SHARED_SRC := \
      facts_smt.cpp \
      facts_coq.cpp \
      facts_summary_builder.cpp 

SMTLATBUILD_SRC := \
      main.cpp

OBJ += ../../util/util$(LIBEXT)

SRC := ${SMTLATBUILD_SRC} ${SHARED_SRC}

include ../../common

INCLUDES :=  -I ../../ -I ../../util

LIBS =

CXXFLAGS += -std=c++11 -MMD -MP -DPRODUCE_PROOF -DIGNORE_DL_THEORYPROPAGATION -DOSMT1_SUBSTITUTION -DCUSTOM_EL_ALLOC -DTERMS_HAVE_EXPLANATIONS -DUSE_GZ -DFULL_LABELING $(INCLUDES)

all: extractsum$(EXEEXT) 


###############################################################################

extractsum$(EXEEXT): $(OBJ)
	$(LINKBIN) -O0 -g -lopensmt2 -lgmp -lgmpxx -lz -lreadline 

clean:
	rm -f *.o *.d extractsum __omega_* __calltree.xml
	rm -f solvers/*.o solvers/*.d

re: clean all
