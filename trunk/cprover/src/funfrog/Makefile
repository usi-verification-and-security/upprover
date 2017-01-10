include ../config.inc

SHARED_SRC := \
      expr_pretty_print.cpp \
      function_info.cpp \
      summary_store.cpp \
      smt_summary_store.cpp \
      prop_summary_store.cpp \
      solvers/satcheck_opensmt2.cpp \
      solvers/smtcheck_opensmt2.cpp \
      solvers/smtcheck_opensmt2_lra.cpp \
      solvers/smt_itp.cpp \
      solvers/prop_itp.cpp

FUNFROG_SRC := \
      partitioning_target_equation.cpp \
      prop_partitioning_target_equation.cpp \
      smt_partitioning_target_equation.cpp \
      partitioning_slice.cpp \
      summary_info.cpp \
      subst_scenario.cpp \
      xml_interface.cpp \
      parseoptions.cpp \
      languages.cpp \
      check_claims.cpp \
      refiner_assertion_sum.cpp \
      prop_refiner_assertion_sum.cpp \
      smt_refiner_assertion_sum.cpp \
      prop_assertion_sum.cpp \
      dependency_checker.cpp \
      prop_dependency_checker.cpp \
      smt_dependency_checker.cpp \
      symex_assertion_sum.cpp \
      summarizing_checker.cpp \
      main.cpp

SUMO_SRC := \
      sumo.cpp

OBJ += ../ansi-c/ansi-c$(LIBEXT) \
      ../cbmc/symex_bmc$(OBJEXT) \
      ../cpp/cpp$(LIBEXT) \
      ../linking/linking$(LIBEXT) \
      ../big-int/big-int$(LIBEXT) \
      ../goto-programs/goto-programs$(LIBEXT) \
      ../goto-symex/goto-symex$(LIBEXT) \
      ../pointer-analysis/value_set$(OBJEXT) \
      ../pointer-analysis/value_set_analysis_fi$(OBJEXT) \
      ../pointer-analysis/value_set_domain_fi$(OBJEXT) \
      ../pointer-analysis/value_set_fi$(OBJEXT) \
      ../pointer-analysis/value_set_dereference$(OBJEXT) \
      ../pointer-analysis/dereference_callback$(OBJEXT) \
      ../pointer-analysis/add_failed_symbols$(OBJEXT) \
      ../pointer-analysis/rewrite_index$(OBJEXT) \
      ../pointer-analysis/goto_program_dereference$(OBJEXT) \
      ../goto-instrument/full_slicer$(OBJEXT) \
      ../goto-instrument/nondet_static$(OBJEXT) \
      ../goto-instrument/cover$(OBJEXT) \
      ../analyses/analyses$(LIBEXT) \
      ../langapi/langapi$(LIBEXT) \
      ../xmllang/xmllang$(LIBEXT) \
      ../assembler/assembler$(LIBEXT) \
      ../solvers/solvers$(LIBEXT) \
      ../util/util$(LIBEXT)

SUMO_OBJ := \
      $(SUMO_SRC:.cpp=$(OBJEXT)) \
      $(OBJ)

SRC := ${FUNFROG_SRC} ${SHARED_SRC}

include ../common

INCLUDES :=  -I .. -I ../util

LIBS =

CXXFLAGS += -std=c++11 -MMD -MP -DPRODUCE_PROOF -DIGNORE_DL_THEORYPROPAGATION -DOSMT1_SUBSTITUTION -DCUSTOM_EL_ALLOC -DTERMS_HAVE_EXPLANATIONS -DUSE_GZ -DFULL_LABELING $(INCLUDES)

all: hifrog-prop$(EXEEXT) 


###############################################################################

hifrog-prop$(EXEEXT): $(OBJ)
	$(LINKBIN) -lopensmt2 -lgmp -lgmpxx -lz -lreadline 

sumo$(EXEEXT): $(SUMO_OBJ)
	$(LINKBIN) -lopensmt2 -lgmp -lgmpxx -lz -lreadline

clean:
	rm -f *.o *.d hifrog sumo __omega_* __calltree.xml
	rm -f solvers/*.o solvers/*.d

re: clean all
