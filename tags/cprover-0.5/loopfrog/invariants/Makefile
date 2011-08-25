SRC = invariant_test.cpp \
      zero_termination.cpp \
      iterator_bounds.cpp \
      iterator_bounds2.cpp \
      string_length.cpp \
      null_pointer.cpp \
      pointer_offset.cpp \
      constant_tracker.cpp \
      pointer_object.cpp \
      strong_bounds.cpp \
      decreasing_length.cpp \
      equalities.cpp \
      inequalities.cpp \
      disequalities.cpp  \
      variable_relations_base.cpp \
      ti_less_greater_all.cpp \
      ti_less_greater_numeric.cpp \
      ti_or_less_greater_all.cpp \
      ti_max_less_greater.cpp \
      ti_sum_less_greater.cpp \
      sti_gzero_implies_less_greater_all.cpp \
      sti_gzero_implies_or_less_greater_all.cpp 
      

OBJ = $(SRC:.cpp=.o)

INCLUDES= -I ../.. -I ../../util -I ..

all: invariants.o

include ../../config.inc
include ../../common

###############################################################################

invariants.o: $(OBJ)
	$(LD) -r -o invariants.o $(OBJ)
  
clean:
	rm -f *.o invariants.o
