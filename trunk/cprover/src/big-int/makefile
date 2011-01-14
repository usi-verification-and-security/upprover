RM = rm -f
OBJ = bigint-test.o bigint-func.o bigint.o
PRG = test-bigint

all : $(PRG)

include ../config.inc
include ../common

clean :
	$(RM) $(OBJ) $(PRG)

.cc.o:
	$(CPLUS) -c $(CPLUSFLAGS) -o $@ $<

$(PRG) : $(OBJ)
	$(CPLUS) $(CPLUSFLAGS) -o $(PRG) $(OBJ)

dep:
