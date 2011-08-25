SRC = satabs.cpp cmdline_options.cpp cegar_loop.cpp \
      safety.cpp satabs_safety_checker.cpp \
      \
      ../cbmc/xml_interface.cpp \
      \
      prepare/prepare.cpp \
      prepare/map_vars.cpp \
      prepare/concrete_model.cpp \
      prepare/languages.cpp \
      prepare/prepare_functions.cpp \
      \
      refiner/add_invariants.cpp \
      refiner/substitute_invariants.cpp \
      refiner/refiner.cpp \
      refiner/refiner_wp.cpp \
      refiner/refiner_wp_async.cpp \
      refiner/refiner_lifter.cpp \
      refiner/transition_refiner.cpp \
      refiner/transition_cache.cpp \
      refiner/select_refiner.cpp \
      \
      modelchecker/modelchecker.cpp \
      \
      abstractor/predicates.cpp \
      abstractor/abstract_program.cpp \
      abstractor/abstractor.cpp \
      abstractor/abstractor_wp.cpp \
      abstractor/abstractor_satqe.cpp \
      abstractor/abstractor_prover.cpp \
      abstractor/discover_predicates.cpp \
      abstractor/canonicalize.cpp \
      abstractor/abstract_expression.cpp \
      abstractor/predabs_aux.cpp \
      abstractor/lift_if.cpp \
      abstractor/initial_abstraction.cpp \
      abstractor/abstract_dynamic_objects.cpp \
      abstractor/abstract_model.cpp \
      abstractor/select_abstractor.cpp \
      \
      modelchecker/abstract_counterexample.cpp \
      modelchecker/abstract_state.cpp \
      modelchecker/modelchecker_boolean_program.cpp \
      modelchecker/select_modelchecker.cpp \
      modelchecker/modelchecker_smv.cpp \
      modelchecker/modelchecker_spin.cpp \
      \
      simulator/select_simulator.cpp \
      simulator/simulator_symex.cpp \
      simulator/concrete_counterexample.cpp \
      simulator/simulator_loop_detection.cpp \
      simulator/recurrence_solver.cpp \
      simulator/path_slicer.cpp

OBJ = $(SRC:.cpp=.o) \
      ../ansi-c/ansi-c.o \
      ../big-int/bigint.o \
      ../goto-symex/goto-symex.o \
      ../intrep/intrep.o \
      ../solvers/solvers.o \
      ../smvlang/smvlang.o \
      ../bplang/bplang.o \
      ../promela/promela.o \
      ../xmllang/xmllang.o \
      ../util/util.o \
      ../goto-programs/goto-programs.o \
      ../pointer-analysis/pointer-analysis.o \
      ../langapi/langapi.o

LIBS =

all: satabs

include ../config.inc
include ../common

ifneq ($(SQUOLEM2),)
CPLUSFLAGS += -DHAVE_QBF_CORE
else
ifneq ($(CUDD),)
CPLUSFLAGS += -DHAVE_QBF_CORE
endif
endif

INCLUDES= -I .. -I ../util 

ifdef MODULE_PROVER
  CPLUSFLAGS += -DHAVE_PROVER
  OBJ += ../prover/prover.o
  SRC += abstractor/predicate_image_prover.cpp
endif

ifdef MODULE_IPP
  CPLUSFLAGS += -DHAVE_IPP
  OBJ += ../ipp/ipp.o
  SRC += refiner/refiner_ipp.cpp simulator/simulator_ipp.cpp
endif

ifdef MODULE_SATQE
  CPLUSFLAGS += -DHAVE_SATQE
  SRC += abstractor/predicate_image_satqe.cpp
  OBJ += ../satqe/satqe.a
endif

ifdef MODULE_CPP
  OBJ += ../cpp/cpp.o
  CPLUSFLAGS += -DHAVE_CPP
endif

ifdef MODULE_SPECC
  OBJ += ../specc/specc.o
  CPLUSFLAGS += -DHAVE_SPECC
endif

ifdef MODULE_PHP
  OBJ += ../php/php.o
  CPLUSFLAGS += -DHAVE_PHP
endif

ifdef MODULE_QBF_CORE
  CPLUSFLAGS += -DQBF_CORE
endif

###############################################################################

satabs: $(OBJ)
	$(CPLUS) $(LINKFLAGS) -o satabs $(OBJ) $(LIBS) 

clean:
	rm -f abstractor/*.o refiner/*.o simulator/*.o modelchecker/*.o \
              *.o satabs prepare/*.o termination/*.o
