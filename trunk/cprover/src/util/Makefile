SRC = arith_tools.cpp base_type.cpp cmdline.cpp config.cpp context.cpp \
      expr.cpp expr_util.cpp i2string.cpp irep.cpp language.cpp \
      lispexpr.cpp lispirep.cpp location.cpp message.cpp language_file.cpp \
      mp_arith.cpp namespace.cpp parseoptions.cpp rename.cpp \
      replace_expr.cpp threeval.cpp typecheck.cpp graph.cpp \
      type.cpp cnf_simplify.cpp str_getline.cpp strstream2string.cpp \
      bitvector.cpp parser.cpp map_util.cpp replace_symbol.cpp actuals.cpp \
      get_module.cpp string_hash.cpp string_container.cpp identifier.cpp \
      rational.cpp options.cpp c_misc.cpp simplify_expr.cpp dstring.cpp \
      find_symbols.cpp rational_tools.cpp ui_message.cpp simplify_utils.cpp \
      time_stopping.cpp symbol.cpp \
      type_eq.cpp guard.cpp array_name.cpp gcd.cpp message_stream.cpp \
      substitute.cpp decision_procedure.cpp union_find.cpp pretty_names.cpp \
      xml.cpp xml_irep.cpp std_types.cpp std_code.cpp \
      format_constant.cpp find_macros.cpp ref_expr_set.cpp std_expr.cpp \
      irep_serialization.cpp symbol_serialization.cpp fixedbv.cpp \
      ieee_float.cpp signal_catcher.cpp pointer_offset_size.cpp \
      bv_arithmetic.cpp tempdir.cpp tempfile.cpp timer.cpp \
      irep_ids.cpp

OBJ = $(SRC:.cpp=.o)

INCLUDES= -I .. -I .

all: util.o ieee_float_test

include ../config.inc
include ../common

ifdef MODULE_FLOATBV
  CPLUSFLAGS += -DHAVE_FLOATBV
endif

###############################################################################
irep_ids.h: irep_ids_convert irep_ids.txt
	./irep_ids_convert header < irep_ids.txt > irep_ids.h

irep_ids.inc: irep_ids_convert irep_ids.txt
	./irep_ids_convert table < irep_ids.txt > irep_ids.inc

irep_ids.cpp: irep_ids.inc irep_ids.h

irep_ids_convert: irep_ids_convert.o
	$(CPLUS) $(LINKFLAGS) -o irep_ids_convert irep_ids_convert.o

$(OBJ): irep_ids.h

util.o: $(OBJ)
	$(LD) $(LDFLAGS) -o util.o $(OBJ)

clean:
	rm -f *.o ieee_float_test irep_ids.h irep_ids.inc irep_ids_convert

ieee_float_test.o: irep_ids.h  

ieee_float_test: ieee_float_test.o ieee_float.o util.o
	$(CPLUS) $(LINKFLAGS) -o ieee_float_test util.o ieee_float_test.o ../big-int/bigint.o
