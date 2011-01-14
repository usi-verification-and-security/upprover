CC     = gcc
CPLUS  = g++
LD     = ld
AR     = ar
YACC   = bison -y
YFLAGS = -v
LEX    = flex
#CC     = icc
#CPLUS  = icpc

# Linux etc.
GCCFLAGS = -Wall -MMD -O2
LINKFLAGS =
LDFLAGS = -r

# MacOS Fat Binaries
# GCCFLAGS = -Wall -MMD -O2 -force_cpusubtype_ALL -arch i386 -arch ppc -arch x86_64
# LINKFLAGS = -force_cpusubtype_ALL -arch i386 -arch ppc -arch x86_64

# use these for Cygwin:
# GCCFLAGS = -Wall -MMD -O2 -mno-cygwin
# LINKFLAGS = -mno-cygwin
# LDFLAGS = -r

# SAT-solvers we have
#CHAFF = ../../zChaff
#BOOLEFORCE = ../../booleforce-0.4
#MINISAT = ../../MiniSat-p_v1.14
MINISAT2 = ../../minisat2
#SMVSAT =

LANGUAGES = ansi-c csp intrep pvs smvlang verilog vhdl netlist cpp specc \
            xmllang promela pascal bplang csharp smtlang nsf mdllang java

# modules that we have
#MODULE_PROVER = 1
#MODULE_IPP = 1
#MODULE_INTERPOLATION = 1
MODULE_BV_REFINEMENT = 1
#MODULE_SATQE = 1
MODULE_CPP = 1
MODULE_SMTLANG = 1
MODULE_SPECC = 1
MODULE_VERILOG = 1
MODULE_VHDL = 1
MODULE_PASCAL = 1
#MODULE_PHP = 1
MODULE_SIMPLIFYLANG = 1
MODULE_HW_CBMC = 1
MODULE_CEMC = 1
MODULE_FLOATBV = 1
MODULE_SMV = 1
