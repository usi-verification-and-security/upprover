include ../config.inc

SHARED_SRC := \
      expr_pretty_print.cpp \
      function_info.cpp \
      summary_store.cpp \
      solvers/satcheck_opensmt2.cpp \
      solvers/prop_itp.cpp

FUNFROG_SRC := \
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
      main.cpp

SUMO_SRC := \
      sumo.cpp

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

SRC := ${FUNFROG_SRC} ${SUMO_SRC} 

include ../common

INCLUDES :=  -I .. -I ../util 

CXXFLAGS := -std=c++11 -DPRODUCE_PROOF -DIGNORE_DL_THEORYPROPAGATION -DOSMT1_SUBSTITUTION -DCUSTOM_EL_ALLOC -DTERMS_HAVE_EXPLANATIONS -DUSE_GZ -DFULL_LABELING $(INCLUDES)

all: hifrog$(EXEEXT) 



###############################################################################

hifrog$(EXEEXT): $(FUNFROG_OBJ)
	$(LINKBIN) -lopensmt2 -lgmp -lgmpxx -lz -lreadline 

sumo$(EXEEXT): $(SUMO_OBJ)
	$(LINKBIN) -lopensmt2 -lgmp -lgmpxx -lz -lreadline

clean:
	rm -f *.o *.d hifrog sumo __omega_* __calltree.xml
	rm -f solvers/*.o solvers/*.d

re: clean all
