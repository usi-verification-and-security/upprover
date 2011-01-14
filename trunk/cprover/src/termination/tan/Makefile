BASEDIR=../..

SRC = main.cpp \
      tan.cpp \
      languages.cpp

OBJ = $(SRC:.cpp=.o) \
      $(BASEDIR)/big-int/bigint.o \
      $(BASEDIR)/goto-programs/goto-programs.o \
      $(BASEDIR)/goto-symex/goto-symex.o \
      $(BASEDIR)/pointer-analysis/pointer-analysis.o \
      $(BASEDIR)/solvers/solvers.o \
      $(BASEDIR)/util/util.o \
      $(BASEDIR)/termination/termination.o \
      \
      $(BASEDIR)/langapi/langapi.o \
      $(BASEDIR)/ansi-c/ansi-c.o \
      $(BASEDIR)/bplang/bplang.o \
      $(BASEDIR)/promela/promela.o \
      $(BASEDIR)/smvlang/smvlang.o \
      \
      $(BASEDIR)/satabs/cmdline_options.o \
      $(BASEDIR)/satabs/cegar_loop.o \
      $(BASEDIR)/satabs/safety.o \
      $(BASEDIR)/satabs/satabs_safety_checker.o \
      \
      $(BASEDIR)/satabs/prepare/prepare.o \
      $(BASEDIR)/satabs/prepare/map_vars.o \
      $(BASEDIR)/satabs/prepare/concrete_model.o \
      $(BASEDIR)/satabs/prepare/languages.o \
      $(BASEDIR)/satabs/prepare/prepare_functions.o \
      \
      $(BASEDIR)/satabs/refiner/add_invariants.o \
      $(BASEDIR)/satabs/refiner/substitute_invariants.o \
      $(BASEDIR)/satabs/refiner/refiner.o \
      $(BASEDIR)/satabs/refiner/refiner_wp.o \
      $(BASEDIR)/satabs/refiner/refiner_wp_async.o \
      $(BASEDIR)/satabs/refiner/refiner_lifter.o \
      $(BASEDIR)/satabs/refiner/transition_refiner.o \
      $(BASEDIR)/satabs/refiner/transition_cache.o \
      $(BASEDIR)/satabs/refiner/select_refiner.o \
      $(BASEDIR)/satabs/refiner/trans_wp.o \
      \
      $(BASEDIR)/satabs/modelchecker/modelchecker.o \
      \
      $(BASEDIR)/satabs/abstractor/predicates.o \
      $(BASEDIR)/satabs/abstractor/abstract_program.o \
      $(BASEDIR)/satabs/abstractor/abstractor.o \
      $(BASEDIR)/satabs/abstractor/abstractor_wp.o \
      $(BASEDIR)/satabs/abstractor/abstractor_satqe.o \
      $(BASEDIR)/satabs/abstractor/abstractor_prover.o \
      $(BASEDIR)/satabs/abstractor/discover_predicates.o \
      $(BASEDIR)/satabs/abstractor/canonicalize.o \
      $(BASEDIR)/satabs/abstractor/abstract_expression.o \
      $(BASEDIR)/satabs/abstractor/predabs_aux.o \
      $(BASEDIR)/satabs/abstractor/lift_if.o \
      $(BASEDIR)/satabs/abstractor/initial_abstraction.o \
      $(BASEDIR)/satabs/abstractor/abstract_dynamic_objects.o \
      $(BASEDIR)/satabs/abstractor/abstract_model.o \
      $(BASEDIR)/satabs/abstractor/select_abstractor.o \
      \
      $(BASEDIR)/satabs/modelchecker/abstract_counterexample.o \
      $(BASEDIR)/satabs/modelchecker/abstract_state.o \
      $(BASEDIR)/satabs/modelchecker/modelchecker_boolean_program.o \
      $(BASEDIR)/satabs/modelchecker/select_modelchecker.o \
      $(BASEDIR)/satabs/modelchecker/modelchecker_smv.o \
      $(BASEDIR)/satabs/modelchecker/modelchecker_spin.o \
      \
      $(BASEDIR)/satabs/simulator/select_simulator.o \
      $(BASEDIR)/satabs/simulator/simulator_symex.o \
      $(BASEDIR)/satabs/simulator/concrete_counterexample.o \
      $(BASEDIR)/satabs/simulator/simulator_loop_detection.o \
      $(BASEDIR)/satabs/simulator/recurrence_solver.o \
      $(BASEDIR)/satabs/simulator/path_slicer.o

INCLUDES= -I $(BASEDIR)/$(CHAFF) -I $(BASEDIR) -I $(BASEDIR)/util

LIBS =

all: tan

include $(BASEDIR)/config.inc
include $(BASEDIR)/common

ifdef MODULE_CPP
  OBJ += $(BASEDIR)/cpp/cpp.o
  CPLUSFLAGS += -DHAVE_CPP
endif

ifdef MODULE_SPECC
  OBJ += $(BASEDIR)/specc/specc.o
  CPLUSFLAGS += -DHAVE_SPECC
endif

ifdef MODULE_INTERPOLATION
  CPLUSFLAGS += -DHAVE_INTERPOLATION
endif


###############################################################################

tan: $(OBJ)
	$(CPLUS) $(LINKFLAGS) -o tan $(OBJ) $(LIBS)

clean:
	rm -f *.o tan
