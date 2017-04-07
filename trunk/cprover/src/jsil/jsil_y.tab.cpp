/* A Bison parser, made by GNU Bison 3.0.2.  */

/* Bison implementation for Yacc-like parsers in C

   Copyright (C) 1984, 1989-1990, 2000-2013 Free Software Foundation, Inc.

   This program is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <http://www.gnu.org/licenses/>.  */

/* As a special exception, you may create a larger work that contains
   part or all of the Bison parser skeleton and distribute that work
   under terms of your choice, so long as that work isn't itself a
   parser generator using the skeleton or a modified version thereof
   as a parser skeleton.  Alternatively, if you modify or redistribute
   the parser skeleton itself, you may (at your option) remove this
   special exception, which will cause the skeleton and the resulting
   Bison output files to be licensed under the GNU General Public
   License without this special exception.

   This special exception was added by the Free Software Foundation in
   version 2.2 of Bison.  */

/* C LALR(1) parser skeleton written by Richard Stallman, by
   simplifying the original so-called "semantic" parser.  */

/* All symbols defined below should begin with yy or YY, to avoid
   infringing on user name space.  This should be done even for local
   variables, as they might otherwise be expanded by user macros.
   There are some unavoidable exceptions within include files to
   define necessary library symbols; they are noted "INFRINGES ON
   USER NAME SPACE" below.  */

/* Identify Bison output.  */
#define YYBISON 1

/* Bison version.  */
#define YYBISON_VERSION "3.0.2"

/* Skeleton name.  */
#define YYSKELETON_NAME "yacc.c"

/* Pure parsers.  */
#define YYPURE 0

/* Push parsers.  */
#define YYPUSH 0

/* Pull parsers.  */
#define YYPULL 1


/* Substitute the variable and function names.  */
#define yyparse         yyjsilparse
#define yylex           yyjsillex
#define yyerror         yyjsilerror
#define yydebug         yyjsildebug
#define yynerrs         yyjsilnerrs

#define yylval          yyjsillval
#define yychar          yyjsilchar

/* Copy the first part of user declarations.  */
#line 1 "parser.y" /* yacc.c:339  */


// #define YYDEBUG 1
#define PARSER jsil_parser

#include "jsil_parser.h"

int yyjsillex();
extern char *yyjsiltext;

#define YYSTYPE unsigned
#define YYSTYPE_IS_TRIVIAL 1

#include <util/std_expr.h>
#include <util/std_code.h>

#include <ansi-c/string_constant.h>

#include "jsil_y.tab.h"
/*** token declaration **************************************************/

#line 96 "jsil_y.tab.cpp" /* yacc.c:339  */

# ifndef YY_NULLPTR
#  if defined __cplusplus && 201103L <= __cplusplus
#   define YY_NULLPTR nullptr
#  else
#   define YY_NULLPTR 0
#  endif
# endif

/* Enabling verbose error messages.  */
#ifdef YYERROR_VERBOSE
# undef YYERROR_VERBOSE
# define YYERROR_VERBOSE 1
#else
# define YYERROR_VERBOSE 1
#endif

/* In a future release of Bison, this section will be replaced
   by #include "jsil_y.tab.hpp".  */
#ifndef YY_YYJSIL_JSIL_Y_TAB_HPP_INCLUDED
# define YY_YYJSIL_JSIL_Y_TAB_HPP_INCLUDED
/* Debug traces.  */
#ifndef YYDEBUG
# define YYDEBUG 0
#endif
#if YYDEBUG
extern int yyjsildebug;
#endif

/* Token type.  */
#ifndef YYTOKENTYPE
# define YYTOKENTYPE
  enum yytokentype
  {
    TOK_SCANNER_ERROR = 258,
    TOK_NEWLINE = 259,
    TOK_PROCEDURE = 260,
    TOK_RETURNS = 261,
    TOK_TO = 262,
    TOK_THROWS = 263,
    TOK_EVAL = 264,
    TOK_LABEL = 265,
    TOK_GOTO = 266,
    TOK_SKIP = 267,
    TOK_WITH = 268,
    TOK_NEW = 269,
    TOK_HAS_FIELD = 270,
    TOK_DELETE = 271,
    TOK_PROTO_FIELD = 272,
    TOK_PROTO_OBJ = 273,
    TOK_REF = 274,
    TOK_FIELD = 275,
    TOK_BASE = 276,
    TOK_TYPEOF = 277,
    TOK_NULL = 278,
    TOK_UNDEFINED = 279,
    TOK_EMPTY = 280,
    TOK_TRUE = 281,
    TOK_FALSE = 282,
    TOK_PROTO = 283,
    TOK_FID = 284,
    TOK_SCOPE = 285,
    TOK_CONSTRUCTID = 286,
    TOK_PRIMVALUE = 287,
    TOK_TARGETFUNCTION = 288,
    TOK_CLASS = 289,
    TOK_NUM_TO_STRING = 290,
    TOK_STRING_TO_NUM = 291,
    TOK_NUM_TO_INT32 = 292,
    TOK_NUM_TO_UINT32 = 293,
    TOK_MEMBER_REFERENCE = 294,
    TOK_VARIABLE_REFERENCE = 295,
    TOK_T_NULL = 296,
    TOK_T_UNDEFINED = 297,
    TOK_T_BOOLEAN = 298,
    TOK_T_STRING = 299,
    TOK_T_NUMBER = 300,
    TOK_T_BUILTIN_OBJECT = 301,
    TOK_T_USER_OBJECT = 302,
    TOK_T_OBJECT = 303,
    TOK_T_REFERENCE = 304,
    TOK_DEFEQ = 305,
    TOK_LEQ = 306,
    TOK_AND = 307,
    TOK_OR = 308,
    TOK_SUBTYPE_OF = 309,
    TOK_LEFT_SHIFT = 310,
    TOK_SIGNED_RIGHT_SHIFT = 311,
    TOK_UNSIGNED_RIGHT_SHIFT = 312,
    TOK_NOT = 313,
    TOK_IDENTIFIER = 314,
    TOK_FLOATING = 315,
    TOK_STRING = 316,
    TOK_BUILTIN_LOC = 317,
    TOK_BUILTIN_IDENTIFIER = 318,
    TOK_SPEC_IDENTIFIER = 319
  };
#endif
/* Tokens.  */
#define TOK_SCANNER_ERROR 258
#define TOK_NEWLINE 259
#define TOK_PROCEDURE 260
#define TOK_RETURNS 261
#define TOK_TO 262
#define TOK_THROWS 263
#define TOK_EVAL 264
#define TOK_LABEL 265
#define TOK_GOTO 266
#define TOK_SKIP 267
#define TOK_WITH 268
#define TOK_NEW 269
#define TOK_HAS_FIELD 270
#define TOK_DELETE 271
#define TOK_PROTO_FIELD 272
#define TOK_PROTO_OBJ 273
#define TOK_REF 274
#define TOK_FIELD 275
#define TOK_BASE 276
#define TOK_TYPEOF 277
#define TOK_NULL 278
#define TOK_UNDEFINED 279
#define TOK_EMPTY 280
#define TOK_TRUE 281
#define TOK_FALSE 282
#define TOK_PROTO 283
#define TOK_FID 284
#define TOK_SCOPE 285
#define TOK_CONSTRUCTID 286
#define TOK_PRIMVALUE 287
#define TOK_TARGETFUNCTION 288
#define TOK_CLASS 289
#define TOK_NUM_TO_STRING 290
#define TOK_STRING_TO_NUM 291
#define TOK_NUM_TO_INT32 292
#define TOK_NUM_TO_UINT32 293
#define TOK_MEMBER_REFERENCE 294
#define TOK_VARIABLE_REFERENCE 295
#define TOK_T_NULL 296
#define TOK_T_UNDEFINED 297
#define TOK_T_BOOLEAN 298
#define TOK_T_STRING 299
#define TOK_T_NUMBER 300
#define TOK_T_BUILTIN_OBJECT 301
#define TOK_T_USER_OBJECT 302
#define TOK_T_OBJECT 303
#define TOK_T_REFERENCE 304
#define TOK_DEFEQ 305
#define TOK_LEQ 306
#define TOK_AND 307
#define TOK_OR 308
#define TOK_SUBTYPE_OF 309
#define TOK_LEFT_SHIFT 310
#define TOK_SIGNED_RIGHT_SHIFT 311
#define TOK_UNSIGNED_RIGHT_SHIFT 312
#define TOK_NOT 313
#define TOK_IDENTIFIER 314
#define TOK_FLOATING 315
#define TOK_STRING 316
#define TOK_BUILTIN_LOC 317
#define TOK_BUILTIN_IDENTIFIER 318
#define TOK_SPEC_IDENTIFIER 319

/* Value type.  */
#if ! defined YYSTYPE && ! defined YYSTYPE_IS_DECLARED
typedef int YYSTYPE;
# define YYSTYPE_IS_TRIVIAL 1
# define YYSTYPE_IS_DECLARED 1
#endif


extern YYSTYPE yyjsillval;

int yyjsilparse (void);

#endif /* !YY_YYJSIL_JSIL_Y_TAB_HPP_INCLUDED  */

/* Copy the second part of user declarations.  */

#line 275 "jsil_y.tab.cpp" /* yacc.c:358  */

#ifdef short
# undef short
#endif

#ifdef YYTYPE_UINT8
typedef YYTYPE_UINT8 yytype_uint8;
#else
typedef unsigned char yytype_uint8;
#endif

#ifdef YYTYPE_INT8
typedef YYTYPE_INT8 yytype_int8;
#else
typedef signed char yytype_int8;
#endif

#ifdef YYTYPE_UINT16
typedef YYTYPE_UINT16 yytype_uint16;
#else
typedef unsigned short int yytype_uint16;
#endif

#ifdef YYTYPE_INT16
typedef YYTYPE_INT16 yytype_int16;
#else
typedef short int yytype_int16;
#endif

#ifndef YYSIZE_T
# ifdef __SIZE_TYPE__
#  define YYSIZE_T __SIZE_TYPE__
# elif defined size_t
#  define YYSIZE_T size_t
# elif ! defined YYSIZE_T
#  include <stddef.h> /* INFRINGES ON USER NAME SPACE */
#  define YYSIZE_T size_t
# else
#  define YYSIZE_T unsigned int
# endif
#endif

#define YYSIZE_MAXIMUM ((YYSIZE_T) -1)

#ifndef YY_
# if defined YYENABLE_NLS && YYENABLE_NLS
#  if ENABLE_NLS
#   include <libintl.h> /* INFRINGES ON USER NAME SPACE */
#   define YY_(Msgid) dgettext ("bison-runtime", Msgid)
#  endif
# endif
# ifndef YY_
#  define YY_(Msgid) Msgid
# endif
#endif

#ifndef YY_ATTRIBUTE
# if (defined __GNUC__                                               \
      && (2 < __GNUC__ || (__GNUC__ == 2 && 96 <= __GNUC_MINOR__)))  \
     || defined __SUNPRO_C && 0x5110 <= __SUNPRO_C
#  define YY_ATTRIBUTE(Spec) __attribute__(Spec)
# else
#  define YY_ATTRIBUTE(Spec) /* empty */
# endif
#endif

#ifndef YY_ATTRIBUTE_PURE
# define YY_ATTRIBUTE_PURE   YY_ATTRIBUTE ((__pure__))
#endif

#ifndef YY_ATTRIBUTE_UNUSED
# define YY_ATTRIBUTE_UNUSED YY_ATTRIBUTE ((__unused__))
#endif

#if !defined _Noreturn \
     && (!defined __STDC_VERSION__ || __STDC_VERSION__ < 201112)
# if defined _MSC_VER && 1200 <= _MSC_VER
#  define _Noreturn __declspec (noreturn)
# else
#  define _Noreturn YY_ATTRIBUTE ((__noreturn__))
# endif
#endif

/* Suppress unused-variable warnings by "using" E.  */
#if ! defined lint || defined __GNUC__
# define YYUSE(E) ((void) (E))
#else
# define YYUSE(E) /* empty */
#endif

#if defined __GNUC__ && 407 <= __GNUC__ * 100 + __GNUC_MINOR__
/* Suppress an incorrect diagnostic about yylval being uninitialized.  */
# define YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN \
    _Pragma ("GCC diagnostic push") \
    _Pragma ("GCC diagnostic ignored \"-Wuninitialized\"")\
    _Pragma ("GCC diagnostic ignored \"-Wmaybe-uninitialized\"")
# define YY_IGNORE_MAYBE_UNINITIALIZED_END \
    _Pragma ("GCC diagnostic pop")
#else
# define YY_INITIAL_VALUE(Value) Value
#endif
#ifndef YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
# define YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
# define YY_IGNORE_MAYBE_UNINITIALIZED_END
#endif
#ifndef YY_INITIAL_VALUE
# define YY_INITIAL_VALUE(Value) /* Nothing. */
#endif


#if ! defined yyoverflow || YYERROR_VERBOSE

/* The parser invokes alloca or malloc; define the necessary symbols.  */

# ifdef YYSTACK_USE_ALLOCA
#  if YYSTACK_USE_ALLOCA
#   ifdef __GNUC__
#    define YYSTACK_ALLOC __builtin_alloca
#   elif defined __BUILTIN_VA_ARG_INCR
#    include <alloca.h> /* INFRINGES ON USER NAME SPACE */
#   elif defined _AIX
#    define YYSTACK_ALLOC __alloca
#   elif defined _MSC_VER
#    include <malloc.h> /* INFRINGES ON USER NAME SPACE */
#    define alloca _alloca
#   else
#    define YYSTACK_ALLOC alloca
#    if ! defined _ALLOCA_H && ! defined EXIT_SUCCESS
#     include <stdlib.h> /* INFRINGES ON USER NAME SPACE */
      /* Use EXIT_SUCCESS as a witness for stdlib.h.  */
#     ifndef EXIT_SUCCESS
#      define EXIT_SUCCESS 0
#     endif
#    endif
#   endif
#  endif
# endif

# ifdef YYSTACK_ALLOC
   /* Pacify GCC's 'empty if-body' warning.  */
#  define YYSTACK_FREE(Ptr) do { /* empty */; } while (0)
#  ifndef YYSTACK_ALLOC_MAXIMUM
    /* The OS might guarantee only one guard page at the bottom of the stack,
       and a page size can be as small as 4096 bytes.  So we cannot safely
       invoke alloca (N) if N exceeds 4096.  Use a slightly smaller number
       to allow for a few compiler-allocated temporary stack slots.  */
#   define YYSTACK_ALLOC_MAXIMUM 4032 /* reasonable circa 2006 */
#  endif
# else
#  define YYSTACK_ALLOC YYMALLOC
#  define YYSTACK_FREE YYFREE
#  ifndef YYSTACK_ALLOC_MAXIMUM
#   define YYSTACK_ALLOC_MAXIMUM YYSIZE_MAXIMUM
#  endif
#  if (defined __cplusplus && ! defined EXIT_SUCCESS \
       && ! ((defined YYMALLOC || defined malloc) \
             && (defined YYFREE || defined free)))
#   include <stdlib.h> /* INFRINGES ON USER NAME SPACE */
#   ifndef EXIT_SUCCESS
#    define EXIT_SUCCESS 0
#   endif
#  endif
#  ifndef YYMALLOC
#   define YYMALLOC malloc
#   if ! defined malloc && ! defined EXIT_SUCCESS
void *malloc (YYSIZE_T); /* INFRINGES ON USER NAME SPACE */
#   endif
#  endif
#  ifndef YYFREE
#   define YYFREE free
#   if ! defined free && ! defined EXIT_SUCCESS
void free (void *); /* INFRINGES ON USER NAME SPACE */
#   endif
#  endif
# endif
#endif /* ! defined yyoverflow || YYERROR_VERBOSE */


#if (! defined yyoverflow \
     && (! defined __cplusplus \
         || (defined YYSTYPE_IS_TRIVIAL && YYSTYPE_IS_TRIVIAL)))

/* A type that is properly aligned for any stack member.  */
union yyalloc
{
  yytype_int16 yyss_alloc;
  YYSTYPE yyvs_alloc;
};

/* The size of the maximum gap between one aligned stack and the next.  */
# define YYSTACK_GAP_MAXIMUM (sizeof (union yyalloc) - 1)

/* The size of an array large to enough to hold all stacks, each with
   N elements.  */
# define YYSTACK_BYTES(N) \
     ((N) * (sizeof (yytype_int16) + sizeof (YYSTYPE)) \
      + YYSTACK_GAP_MAXIMUM)

# define YYCOPY_NEEDED 1

/* Relocate STACK from its old location to the new one.  The
   local variables YYSIZE and YYSTACKSIZE give the old and new number of
   elements in the stack, and YYPTR gives the new location of the
   stack.  Advance YYPTR to a properly aligned location for the next
   stack.  */
# define YYSTACK_RELOCATE(Stack_alloc, Stack)                           \
    do                                                                  \
      {                                                                 \
        YYSIZE_T yynewbytes;                                            \
        YYCOPY (&yyptr->Stack_alloc, Stack, yysize);                    \
        Stack = &yyptr->Stack_alloc;                                    \
        yynewbytes = yystacksize * sizeof (*Stack) + YYSTACK_GAP_MAXIMUM; \
        yyptr += yynewbytes / sizeof (*yyptr);                          \
      }                                                                 \
    while (0)

#endif

#if defined YYCOPY_NEEDED && YYCOPY_NEEDED
/* Copy COUNT objects from SRC to DST.  The source and destination do
   not overlap.  */
# ifndef YYCOPY
#  if defined __GNUC__ && 1 < __GNUC__
#   define YYCOPY(Dst, Src, Count) \
      __builtin_memcpy (Dst, Src, (Count) * sizeof (*(Src)))
#  else
#   define YYCOPY(Dst, Src, Count)              \
      do                                        \
        {                                       \
          YYSIZE_T yyi;                         \
          for (yyi = 0; yyi < (Count); yyi++)   \
            (Dst)[yyi] = (Src)[yyi];            \
        }                                       \
      while (0)
#  endif
# endif
#endif /* !YYCOPY_NEEDED */

/* YYFINAL -- State number of the termination state.  */
#define YYFINAL  10
/* YYLAST -- Last index in YYTABLE.  */
#define YYLAST   858

/* YYNTOKENS -- Number of terminals.  */
#define YYNTOKENS  84
/* YYNNTS -- Number of nonterminals.  */
#define YYNNTS  28
/* YYNRULES -- Number of rules.  */
#define YYNRULES  109
/* YYNSTATES -- Number of states.  */
#define YYNSTATES  192

/* YYTRANSLATE[YYX] -- Symbol number corresponding to YYX as returned
   by yylex, with out-of-bounds checking.  */
#define YYUNDEFTOK  2
#define YYMAXUTOK   319

#define YYTRANSLATE(YYX)                                                \
  ((unsigned int) (YYX) <= YYMAXUTOK ? yytranslate[YYX] : YYUNDEFTOK)

/* YYTRANSLATE[TOKEN-NUM] -- Symbol number corresponding to TOKEN-NUM
   as returned by yylex, without out-of-bounds checking.  */
static const yytype_uint8 yytranslate[] =
{
       0,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,    83,     2,     2,     2,    78,    80,     2,
      65,    66,    76,    74,    69,    75,     2,    77,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,    79,     2,
      73,    72,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,    70,     2,    71,    82,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,    67,    81,    68,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     1,     2,     3,     4,
       5,     6,     7,     8,     9,    10,    11,    12,    13,    14,
      15,    16,    17,    18,    19,    20,    21,    22,    23,    24,
      25,    26,    27,    28,    29,    30,    31,    32,    33,    34,
      35,    36,    37,    38,    39,    40,    41,    42,    43,    44,
      45,    46,    47,    48,    49,    50,    51,    52,    53,    54,
      55,    56,    57,    58,    59,    60,    61,    62,    63,    64
};

#if YYDEBUG
  /* YYRLINE[YYN] -- Source line where rule number YYN was defined.  */
static const yytype_uint16 yyrline[] =
{
       0,   109,   109,   112,   113,   116,   149,   150,   155,   159,
     165,   166,   174,   177,   180,   185,   193,   196,   199,   205,
     212,   216,   222,   229,   234,   246,   250,   255,   263,   264,
     279,   284,   292,   297,   305,   313,   324,   327,   334,   337,
     340,   345,   352,   353,   361,   362,   367,   371,   380,   387,
     394,   403,   404,   408,   412,   416,   420,   424,   425,   431,
     432,   433,   436,   440,   444,   448,   452,   456,   460,   466,
     467,   468,   469,   472,   476,   480,   486,   490,   494,   498,
     502,   508,   512,   516,   520,   526,   530,   534,   538,   542,
     546,   552,   556,   560,   564,   568,   572,   576,   582,   586,
     590,   594,   598,   602,   606,   610,   614,   615,   621,   625
};
#endif

#if YYDEBUG || YYERROR_VERBOSE || 1
/* YYTNAME[SYMBOL-NUM] -- String name of the symbol SYMBOL-NUM.
   First, the terminals, then, starting at YYNTOKENS, nonterminals.  */
static const char *const yytname[] =
{
  "$end", "error", "$undefined", "TOK_SCANNER_ERROR", "\"<newline>\"",
  "\"procedure\"", "\"returns\"", "\"to\"", "\"throws\"", "\"eval\"",
  "\"label\"", "\"goto\"", "\"skip\"", "\"with\"", "\"new\"",
  "\"hasField\"", "\"delete\"", "\"protoField\"", "\"protoObj\"",
  "\"ref\"", "\"field\"", "\"base\"", "\"typeOf\"", "\"null\"",
  "\"#undefined\"", "\"#empty\"", "\"true\"", "\"false\"", "\"#proto\"",
  "\"#fid\"", "\"#scope\"", "\"#constructid\"", "\"#primvalue\"",
  "\"#targetfunction\"", "\"#class\"", "\"num_to_string\"",
  "\"string_to_num\"", "\"num_to_int32\"", "\"num_to_uint32\"",
  "\"#MemberReference\"", "\"#VariableReference\"", "\"#Null\"",
  "\"#Undefined\"", "\"#Boolean\"", "\"#String\"", "\"#Number\"",
  "\"#BuiltinObject\"", "\"#UserObject\"", "\"#Object\"", "\"#Reference\"",
  "\":=\"", "\"<=\"", "\"and\"", "\"or\"", "\"<:\"", "\"<<\"", "\">>\"",
  "\">>>\"", "\"not\"", "TOK_IDENTIFIER", "TOK_FLOATING", "TOK_STRING",
  "TOK_BUILTIN_LOC", "TOK_BUILTIN_IDENTIFIER", "TOK_SPEC_IDENTIFIER",
  "'('", "')'", "'{'", "'}'", "','", "'['", "']'", "'='", "'<'", "'+'",
  "'-'", "'*'", "'/'", "'%'", "':'", "'&'", "'|'", "'^'", "'!'", "$accept",
  "program", "procedure_decls", "procedure_decl", "proc_ident",
  "proc_ident_expr", "parameters_opt", "parameters", "statements_opt",
  "statements", "statement", "instruction", "rhs", "with_opt",
  "expressions_opt", "expressions", "expression", "atom_expression",
  "literal", "builtin_field", "binary_op", "compare_op", "arithmetic_op",
  "boolean_op", "bitwise_op", "unary_op", "jsil_type", "ref_type", YY_NULLPTR
};
#endif

# ifdef YYPRINT
/* YYTOKNUM[NUM] -- (External) token number corresponding to the
   (internal) symbol number NUM (which must be that of a token).  */
static const yytype_uint16 yytoknum[] =
{
       0,   256,   257,   258,   259,   260,   261,   262,   263,   264,
     265,   266,   267,   268,   269,   270,   271,   272,   273,   274,
     275,   276,   277,   278,   279,   280,   281,   282,   283,   284,
     285,   286,   287,   288,   289,   290,   291,   292,   293,   294,
     295,   296,   297,   298,   299,   300,   301,   302,   303,   304,
     305,   306,   307,   308,   309,   310,   311,   312,   313,   314,
     315,   316,   317,   318,   319,    40,    41,   123,   125,    44,
      91,    93,    61,    60,    43,    45,    42,    47,    37,    58,
      38,   124,    94,    33
};
# endif

#define YYPACT_NINF -147

#define yypact_value_is_default(Yystate) \
  (!!((Yystate) == (-147)))

#define YYTABLE_NINF -12

#define yytable_value_is_error(Yytable_value) \
  0

  /* YYPACT[STATE-NUM] -- Index in YYTABLE of the portion describing
     STATE-NUM.  */
static const yytype_int16 yypact[] =
{
       0,    -3,     7,     0,  -147,  -147,  -147,  -147,  -147,   -52,
    -147,  -147,   -45,  -147,   -50,   -51,    11,   -39,   -38,  -147,
      12,   -37,    15,   -35,    18,   -33,   -36,    -2,  -147,   -32,
     -55,  -147,   -22,   185,   -34,    -2,  -147,    25,  -147,  -147,
     185,   120,   -30,   -29,   -26,   -25,  -147,  -147,  -147,  -147,
    -147,  -147,  -147,  -147,  -147,  -147,  -147,  -147,  -147,  -147,
    -147,  -147,  -147,  -147,  -147,  -147,  -147,  -147,  -147,  -147,
    -147,  -147,  -147,  -147,  -147,  -147,  -147,  -147,   185,  -147,
    -147,    31,  -147,  -147,  -147,   185,  -147,  -147,  -147,  -147,
    -147,   200,   -24,   -23,   -21,   -20,   -18,   -17,   -16,   185,
    -147,   -15,  -147,   776,   185,   185,   185,   185,   232,  -147,
    -147,  -147,  -147,  -147,  -147,  -147,   185,  -147,  -147,  -147,
    -147,  -147,  -147,  -147,  -147,  -147,  -147,  -147,   185,  -147,
    -147,  -147,  -147,  -147,   -27,   -14,   185,   185,   185,   185,
     264,   185,   296,   328,   360,   392,  -147,   424,  -147,   -11,
    -147,   456,   488,   520,   552,   185,   -13,    -7,   776,   185,
    -147,  -147,  -147,     1,    -5,   185,   185,   185,   185,   584,
      17,   185,   616,   185,  -147,   648,   680,   712,   744,  -147,
      -4,  -147,   776,   -28,   776,  -147,  -147,  -147,  -147,  -147,
       3,  -147
};

  /* YYDEFACT[STATE-NUM] -- Default reduction number in state STATE-NUM.
     Performed when YYTABLE does not specify something else to do.  Zero
     means the default is an error.  */
static const yytype_uint8 yydefact[] =
{
       0,     0,     0,     2,     3,     7,     6,     8,     9,     0,
       1,     4,    12,    14,     0,    13,     0,     0,     0,    15,
       0,     0,     0,     0,     0,     0,     0,    16,    20,     0,
       0,    25,     0,     0,     0,    17,    18,     0,    22,    23,
       0,     0,     0,     0,     0,     0,    52,    53,    54,    55,
      56,    62,    63,    64,    65,    66,    67,    68,    93,    94,
      95,    96,   108,   109,    98,    99,   100,   101,   102,   103,
     104,   105,   107,    91,    51,    57,    58,    59,     0,    92,
      97,     0,    42,    44,    61,     0,    60,   106,     5,    19,
      21,     0,     0,     0,     0,     0,     0,    51,    58,     0,
      10,     0,    26,    28,     0,     0,     0,     0,     0,    75,
      81,    82,    83,    88,    89,    90,     0,    73,    74,    76,
      77,    78,    79,    80,    84,    85,    86,    87,     0,    69,
      70,    71,    72,    45,     0,     0,     0,     0,     0,     0,
       0,    38,     0,     0,     0,     0,    46,     0,    43,     0,
      30,     0,     0,     0,     0,     0,     0,    39,    40,     0,
      48,    49,    50,     0,     0,     0,     0,     0,     0,     0,
      36,     0,     0,     0,    24,     0,     0,     0,     0,    32,
       0,    29,    41,     0,    27,    31,    33,    34,    35,    37,
       0,    47
};

  /* YYPGOTO[NTERM-NUM].  */
static const yytype_int16 yypgoto[] =
{
    -147,  -147,  -147,    30,     2,  -147,  -147,  -147,  -147,  -147,
      28,  -147,  -147,  -147,  -147,  -147,   -40,   -82,  -147,  -147,
    -147,  -147,  -147,  -147,  -147,  -147,  -147,  -146
};

  /* YYDEFGOTO[NTERM-NUM].  */
static const yytype_int16 yydefgoto[] =
{
      -1,     2,     3,     4,     9,   101,    14,    15,    34,    35,
      36,    37,   102,   181,   156,   157,    81,    82,    83,    84,
     128,   129,   130,   131,   132,    85,    86,    87
};

  /* YYTABLE[YYPACT[STATE-NUM]] -- What to do in state STATE-NUM.  If
     positive, shift that token.  If negative, reduce the rule whose
     number is the opposite.  If YYTABLE_NINF, syntax error.  */
static const yytype_int16 yytable[] =
{
      91,   103,    28,   133,    39,     1,     5,    10,    29,    30,
      31,    62,    63,    12,    13,    40,    16,    18,    17,    21,
      19,    20,    22,    23,    24,    25,    26,    38,    41,    90,
     180,    27,   149,    11,    88,   104,   105,   190,   108,   106,
     107,   135,   136,   100,   137,   138,   148,   139,    -6,   -11,
     141,   173,   150,   170,   174,   189,     6,    32,   164,   140,
       7,     8,   171,    89,   142,   143,   144,   145,    33,   191,
       0,     0,     0,     0,     0,     0,   147,     0,     0,     0,
       0,     0,   109,   110,   111,   112,   113,   114,   115,     0,
       0,     0,     0,     0,     0,     0,   151,   152,   153,   154,
     116,   158,     0,   117,   118,   119,   120,   121,   122,   123,
     124,   125,   126,   127,     0,   169,     0,     0,     0,   172,
       0,     0,     0,     0,     0,   175,   176,   177,   178,     5,
       0,   182,     0,   184,    92,    93,    94,    95,    96,    42,
      43,    44,    45,    46,    47,    48,    49,    50,    51,    52,
      53,    54,    55,    56,    57,    58,    59,    60,    61,    62,
      63,    64,    65,    66,    67,    68,    69,    70,    71,    72,
       0,     0,     0,     0,     0,     0,     0,     0,    73,    97,
      75,    98,    77,     7,     8,    78,     0,     0,     0,     0,
      99,     0,     0,     0,     0,    79,     0,     0,     0,     0,
       0,     0,     0,    80,    42,    43,    44,    45,    46,    47,
      48,    49,    50,    51,    52,    53,    54,    55,    56,    57,
      58,    59,    60,    61,    62,    63,    64,    65,    66,    67,
      68,    69,    70,    71,    72,     0,     0,     0,     0,     0,
       0,     0,     0,    73,    74,    75,    76,    77,     0,     0,
      78,   109,   110,   111,   112,   113,   114,   115,     0,     0,
      79,     0,     0,     0,     0,     0,     0,     0,    80,     0,
       0,   134,   117,   118,   119,   120,   121,   122,   123,   124,
     125,   126,   127,   109,   110,   111,   112,   113,   114,   115,
       0,     0,     0,     0,     0,     0,     0,     0,   146,     0,
       0,     0,     0,     0,   117,   118,   119,   120,   121,   122,
     123,   124,   125,   126,   127,   109,   110,   111,   112,   113,
     114,   115,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,   155,     0,     0,   117,   118,   119,   120,
     121,   122,   123,   124,   125,   126,   127,   109,   110,   111,
     112,   113,   114,   115,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,   159,     0,     0,   117,   118,
     119,   120,   121,   122,   123,   124,   125,   126,   127,   109,
     110,   111,   112,   113,   114,   115,     0,     0,     0,     0,
       0,     0,     0,     0,   160,     0,     0,     0,     0,     0,
     117,   118,   119,   120,   121,   122,   123,   124,   125,   126,
     127,   109,   110,   111,   112,   113,   114,   115,     0,     0,
       0,     0,     0,     0,     0,     0,   161,     0,     0,     0,
       0,     0,   117,   118,   119,   120,   121,   122,   123,   124,
     125,   126,   127,   109,   110,   111,   112,   113,   114,   115,
       0,     0,     0,     0,     0,     0,     0,     0,   162,     0,
       0,     0,     0,     0,   117,   118,   119,   120,   121,   122,
     123,   124,   125,   126,   127,   109,   110,   111,   112,   113,
     114,   115,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,   163,   117,   118,   119,   120,
     121,   122,   123,   124,   125,   126,   127,   109,   110,   111,
     112,   113,   114,   115,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,   165,     0,     0,   117,   118,
     119,   120,   121,   122,   123,   124,   125,   126,   127,   109,
     110,   111,   112,   113,   114,   115,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,   166,     0,     0,
     117,   118,   119,   120,   121,   122,   123,   124,   125,   126,
     127,   109,   110,   111,   112,   113,   114,   115,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,   167,
       0,     0,   117,   118,   119,   120,   121,   122,   123,   124,
     125,   126,   127,   109,   110,   111,   112,   113,   114,   115,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,   168,     0,     0,   117,   118,   119,   120,   121,   122,
     123,   124,   125,   126,   127,   109,   110,   111,   112,   113,
     114,   115,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,   179,   117,   118,   119,   120,
     121,   122,   123,   124,   125,   126,   127,   109,   110,   111,
     112,   113,   114,   115,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,   183,     0,     0,   117,   118,
     119,   120,   121,   122,   123,   124,   125,   126,   127,   109,
     110,   111,   112,   113,   114,   115,     0,     0,     0,     0,
       0,     0,     0,     0,   185,     0,     0,     0,     0,     0,
     117,   118,   119,   120,   121,   122,   123,   124,   125,   126,
     127,   109,   110,   111,   112,   113,   114,   115,     0,     0,
       0,     0,     0,     0,     0,     0,   186,     0,     0,     0,
       0,     0,   117,   118,   119,   120,   121,   122,   123,   124,
     125,   126,   127,   109,   110,   111,   112,   113,   114,   115,
       0,     0,     0,     0,     0,     0,     0,     0,   187,     0,
       0,     0,     0,     0,   117,   118,   119,   120,   121,   122,
     123,   124,   125,   126,   127,   109,   110,   111,   112,   113,
     114,   115,     0,     0,     0,     0,     0,     0,     0,     0,
     188,     0,     0,     0,     0,     0,   117,   118,   119,   120,
     121,   122,   123,   124,   125,   126,   127,   109,   110,   111,
     112,   113,   114,   115,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,   117,   118,
     119,   120,   121,   122,   123,   124,   125,   126,   127
};

static const yytype_int16 yycheck[] =
{
      40,    41,     4,    85,    59,     5,     9,     0,    10,    11,
      12,    39,    40,    65,    59,    70,    66,     6,    69,     7,
      59,    59,    59,     8,    59,     7,    59,    59,    50,     4,
      13,    67,    59,     3,    68,    65,    65,   183,    78,    65,
      65,    65,    65,    41,    65,    65,   128,    65,    65,    65,
      65,    50,    66,    66,    59,    59,    59,    59,    69,    99,
      63,    64,    69,    35,   104,   105,   106,   107,    70,    66,
      -1,    -1,    -1,    -1,    -1,    -1,   116,    -1,    -1,    -1,
      -1,    -1,    51,    52,    53,    54,    55,    56,    57,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,   136,   137,   138,   139,
      69,   141,    -1,    72,    73,    74,    75,    76,    77,    78,
      79,    80,    81,    82,    -1,   155,    -1,    -1,    -1,   159,
      -1,    -1,    -1,    -1,    -1,   165,   166,   167,   168,     9,
      -1,   171,    -1,   173,    14,    15,    16,    17,    18,    19,
      20,    21,    22,    23,    24,    25,    26,    27,    28,    29,
      30,    31,    32,    33,    34,    35,    36,    37,    38,    39,
      40,    41,    42,    43,    44,    45,    46,    47,    48,    49,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    58,    59,
      60,    61,    62,    63,    64,    65,    -1,    -1,    -1,    -1,
      70,    -1,    -1,    -1,    -1,    75,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    83,    19,    20,    21,    22,    23,    24,
      25,    26,    27,    28,    29,    30,    31,    32,    33,    34,
      35,    36,    37,    38,    39,    40,    41,    42,    43,    44,
      45,    46,    47,    48,    49,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    58,    59,    60,    61,    62,    -1,    -1,
      65,    51,    52,    53,    54,    55,    56,    57,    -1,    -1,
      75,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    83,    -1,
      -1,    71,    72,    73,    74,    75,    76,    77,    78,    79,
      80,    81,    82,    51,    52,    53,    54,    55,    56,    57,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    66,    -1,
      -1,    -1,    -1,    -1,    72,    73,    74,    75,    76,    77,
      78,    79,    80,    81,    82,    51,    52,    53,    54,    55,
      56,    57,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    69,    -1,    -1,    72,    73,    74,    75,
      76,    77,    78,    79,    80,    81,    82,    51,    52,    53,
      54,    55,    56,    57,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    69,    -1,    -1,    72,    73,
      74,    75,    76,    77,    78,    79,    80,    81,    82,    51,
      52,    53,    54,    55,    56,    57,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    66,    -1,    -1,    -1,    -1,    -1,
      72,    73,    74,    75,    76,    77,    78,    79,    80,    81,
      82,    51,    52,    53,    54,    55,    56,    57,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    66,    -1,    -1,    -1,
      -1,    -1,    72,    73,    74,    75,    76,    77,    78,    79,
      80,    81,    82,    51,    52,    53,    54,    55,    56,    57,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    66,    -1,
      -1,    -1,    -1,    -1,    72,    73,    74,    75,    76,    77,
      78,    79,    80,    81,    82,    51,    52,    53,    54,    55,
      56,    57,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    71,    72,    73,    74,    75,
      76,    77,    78,    79,    80,    81,    82,    51,    52,    53,
      54,    55,    56,    57,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    69,    -1,    -1,    72,    73,
      74,    75,    76,    77,    78,    79,    80,    81,    82,    51,
      52,    53,    54,    55,    56,    57,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    69,    -1,    -1,
      72,    73,    74,    75,    76,    77,    78,    79,    80,    81,
      82,    51,    52,    53,    54,    55,    56,    57,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    69,
      -1,    -1,    72,    73,    74,    75,    76,    77,    78,    79,
      80,    81,    82,    51,    52,    53,    54,    55,    56,    57,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    69,    -1,    -1,    72,    73,    74,    75,    76,    77,
      78,    79,    80,    81,    82,    51,    52,    53,    54,    55,
      56,    57,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    71,    72,    73,    74,    75,
      76,    77,    78,    79,    80,    81,    82,    51,    52,    53,
      54,    55,    56,    57,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    69,    -1,    -1,    72,    73,
      74,    75,    76,    77,    78,    79,    80,    81,    82,    51,
      52,    53,    54,    55,    56,    57,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    66,    -1,    -1,    -1,    -1,    -1,
      72,    73,    74,    75,    76,    77,    78,    79,    80,    81,
      82,    51,    52,    53,    54,    55,    56,    57,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    66,    -1,    -1,    -1,
      -1,    -1,    72,    73,    74,    75,    76,    77,    78,    79,
      80,    81,    82,    51,    52,    53,    54,    55,    56,    57,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    66,    -1,
      -1,    -1,    -1,    -1,    72,    73,    74,    75,    76,    77,
      78,    79,    80,    81,    82,    51,    52,    53,    54,    55,
      56,    57,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      66,    -1,    -1,    -1,    -1,    -1,    72,    73,    74,    75,
      76,    77,    78,    79,    80,    81,    82,    51,    52,    53,
      54,    55,    56,    57,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    72,    73,
      74,    75,    76,    77,    78,    79,    80,    81,    82
};

  /* YYSTOS[STATE-NUM] -- The (internal number of the) accessing
     symbol of state STATE-NUM.  */
static const yytype_uint8 yystos[] =
{
       0,     5,    85,    86,    87,     9,    59,    63,    64,    88,
       0,    87,    65,    59,    90,    91,    66,    69,     6,    59,
      59,     7,    59,     8,    59,     7,    59,    67,     4,    10,
      11,    12,    59,    70,    92,    93,    94,    95,    59,    59,
      70,    50,    19,    20,    21,    22,    23,    24,    25,    26,
      27,    28,    29,    30,    31,    32,    33,    34,    35,    36,
      37,    38,    39,    40,    41,    42,    43,    44,    45,    46,
      47,    48,    49,    58,    59,    60,    61,    62,    65,    75,
      83,   100,   101,   102,   103,   109,   110,   111,    68,    94,
       4,   100,    14,    15,    16,    17,    18,    59,    61,    70,
      88,    89,    96,   100,    65,    65,    65,    65,   100,    51,
      52,    53,    54,    55,    56,    57,    69,    72,    73,    74,
      75,    76,    77,    78,    79,    80,    81,    82,   104,   105,
     106,   107,   108,   101,    71,    65,    65,    65,    65,    65,
     100,    65,   100,   100,   100,   100,    66,   100,   101,    59,
      66,   100,   100,   100,   100,    69,    98,    99,   100,    69,
      66,    66,    66,    71,    69,    69,    69,    69,    69,   100,
      66,    69,   100,    50,    59,   100,   100,   100,   100,    71,
      13,    97,   100,    69,   100,    66,    66,    66,    66,    59,
     111,    66
};

  /* YYR1[YYN] -- Symbol number of symbol that rule YYN derives.  */
static const yytype_uint8 yyr1[] =
{
       0,    84,    85,    86,    86,    87,    88,    88,    88,    88,
      89,    89,    90,    90,    91,    91,    92,    92,    93,    93,
      94,    94,    95,    95,    95,    95,    95,    95,    96,    96,
      96,    96,    96,    96,    96,    96,    97,    97,    98,    98,
      99,    99,   100,   100,   101,   101,   101,   101,   101,   101,
     101,   102,   102,   102,   102,   102,   102,   102,   102,   102,
     102,   102,   103,   103,   103,   103,   103,   103,   103,   104,
     104,   104,   104,   105,   105,   105,   106,   106,   106,   106,
     106,   107,   107,   107,   107,   108,   108,   108,   108,   108,
     108,   109,   109,   109,   109,   109,   109,   109,   110,   110,
     110,   110,   110,   110,   110,   110,   110,   110,   111,   111
};

  /* YYR2[YYN] -- Number of symbols on the right hand side of rule YYN.  */
static const yytype_uint8 yyr2[] =
{
       0,     2,     1,     1,     2,    16,     1,     1,     1,     1,
       1,     1,     0,     1,     1,     3,     0,     1,     1,     2,
       1,     2,     2,     2,     7,     1,     3,     7,     1,     5,
       3,     6,     5,     6,     6,     6,     0,     2,     0,     1,
       1,     3,     1,     3,     1,     2,     3,     8,     4,     4,
       4,     1,     1,     1,     1,     1,     1,     1,     1,     1,
       1,     1,     1,     1,     1,     1,     1,     1,     1,     1,
       1,     1,     1,     1,     1,     1,     1,     1,     1,     1,
       1,     1,     1,     1,     1,     1,     1,     1,     1,     1,
       1,     1,     1,     1,     1,     1,     1,     1,     1,     1,
       1,     1,     1,     1,     1,     1,     1,     1,     1,     1
};


#define yyerrok         (yyerrstatus = 0)
#define yyclearin       (yychar = YYEMPTY)
#define YYEMPTY         (-2)
#define YYEOF           0

#define YYACCEPT        goto yyacceptlab
#define YYABORT         goto yyabortlab
#define YYERROR         goto yyerrorlab


#define YYRECOVERING()  (!!yyerrstatus)

#define YYBACKUP(Token, Value)                                  \
do                                                              \
  if (yychar == YYEMPTY)                                        \
    {                                                           \
      yychar = (Token);                                         \
      yylval = (Value);                                         \
      YYPOPSTACK (yylen);                                       \
      yystate = *yyssp;                                         \
      goto yybackup;                                            \
    }                                                           \
  else                                                          \
    {                                                           \
      yyerror (YY_("syntax error: cannot back up")); \
      YYERROR;                                                  \
    }                                                           \
while (0)

/* Error token number */
#define YYTERROR        1
#define YYERRCODE       256



/* Enable debugging if requested.  */
#if YYDEBUG

# ifndef YYFPRINTF
#  include <stdio.h> /* INFRINGES ON USER NAME SPACE */
#  define YYFPRINTF fprintf
# endif

# define YYDPRINTF(Args)                        \
do {                                            \
  if (yydebug)                                  \
    YYFPRINTF Args;                             \
} while (0)

/* This macro is provided for backward compatibility. */
#ifndef YY_LOCATION_PRINT
# define YY_LOCATION_PRINT(File, Loc) ((void) 0)
#endif


# define YY_SYMBOL_PRINT(Title, Type, Value, Location)                    \
do {                                                                      \
  if (yydebug)                                                            \
    {                                                                     \
      YYFPRINTF (stderr, "%s ", Title);                                   \
      yy_symbol_print (stderr,                                            \
                  Type, Value); \
      YYFPRINTF (stderr, "\n");                                           \
    }                                                                     \
} while (0)


/*----------------------------------------.
| Print this symbol's value on YYOUTPUT.  |
`----------------------------------------*/

static void
yy_symbol_value_print (FILE *yyoutput, int yytype, YYSTYPE const * const yyvaluep)
{
  FILE *yyo = yyoutput;
  YYUSE (yyo);
  if (!yyvaluep)
    return;
# ifdef YYPRINT
  if (yytype < YYNTOKENS)
    YYPRINT (yyoutput, yytoknum[yytype], *yyvaluep);
# endif
  YYUSE (yytype);
}


/*--------------------------------.
| Print this symbol on YYOUTPUT.  |
`--------------------------------*/

static void
yy_symbol_print (FILE *yyoutput, int yytype, YYSTYPE const * const yyvaluep)
{
  YYFPRINTF (yyoutput, "%s %s (",
             yytype < YYNTOKENS ? "token" : "nterm", yytname[yytype]);

  yy_symbol_value_print (yyoutput, yytype, yyvaluep);
  YYFPRINTF (yyoutput, ")");
}

/*------------------------------------------------------------------.
| yy_stack_print -- Print the state stack from its BOTTOM up to its |
| TOP (included).                                                   |
`------------------------------------------------------------------*/

static void
yy_stack_print (yytype_int16 *yybottom, yytype_int16 *yytop)
{
  YYFPRINTF (stderr, "Stack now");
  for (; yybottom <= yytop; yybottom++)
    {
      int yybot = *yybottom;
      YYFPRINTF (stderr, " %d", yybot);
    }
  YYFPRINTF (stderr, "\n");
}

# define YY_STACK_PRINT(Bottom, Top)                            \
do {                                                            \
  if (yydebug)                                                  \
    yy_stack_print ((Bottom), (Top));                           \
} while (0)


/*------------------------------------------------.
| Report that the YYRULE is going to be reduced.  |
`------------------------------------------------*/

static void
yy_reduce_print (yytype_int16 *yyssp, YYSTYPE *yyvsp, int yyrule)
{
  unsigned long int yylno = yyrline[yyrule];
  int yynrhs = yyr2[yyrule];
  int yyi;
  YYFPRINTF (stderr, "Reducing stack by rule %d (line %lu):\n",
             yyrule - 1, yylno);
  /* The symbols being reduced.  */
  for (yyi = 0; yyi < yynrhs; yyi++)
    {
      YYFPRINTF (stderr, "   $%d = ", yyi + 1);
      yy_symbol_print (stderr,
                       yystos[yyssp[yyi + 1 - yynrhs]],
                       &(yyvsp[(yyi + 1) - (yynrhs)])
                                              );
      YYFPRINTF (stderr, "\n");
    }
}

# define YY_REDUCE_PRINT(Rule)          \
do {                                    \
  if (yydebug)                          \
    yy_reduce_print (yyssp, yyvsp, Rule); \
} while (0)

/* Nonzero means print parse trace.  It is left uninitialized so that
   multiple parsers can coexist.  */
int yydebug;
#else /* !YYDEBUG */
# define YYDPRINTF(Args)
# define YY_SYMBOL_PRINT(Title, Type, Value, Location)
# define YY_STACK_PRINT(Bottom, Top)
# define YY_REDUCE_PRINT(Rule)
#endif /* !YYDEBUG */


/* YYINITDEPTH -- initial size of the parser's stacks.  */
#ifndef YYINITDEPTH
# define YYINITDEPTH 200
#endif

/* YYMAXDEPTH -- maximum size the stacks can grow to (effective only
   if the built-in stack extension method is used).

   Do not make this value too large; the results are undefined if
   YYSTACK_ALLOC_MAXIMUM < YYSTACK_BYTES (YYMAXDEPTH)
   evaluated with infinite-precision integer arithmetic.  */

#ifndef YYMAXDEPTH
# define YYMAXDEPTH 10000
#endif


#if YYERROR_VERBOSE

# ifndef yystrlen
#  if defined __GLIBC__ && defined _STRING_H
#   define yystrlen strlen
#  else
/* Return the length of YYSTR.  */
static YYSIZE_T
yystrlen (const char *yystr)
{
  YYSIZE_T yylen;
  for (yylen = 0; yystr[yylen]; yylen++)
    continue;
  return yylen;
}
#  endif
# endif

# ifndef yystpcpy
#  if defined __GLIBC__ && defined _STRING_H && defined _GNU_SOURCE
#   define yystpcpy stpcpy
#  else
/* Copy YYSRC to YYDEST, returning the address of the terminating '\0' in
   YYDEST.  */
static char *
yystpcpy (char *yydest, const char *yysrc)
{
  char *yyd = yydest;
  const char *yys = yysrc;

  while ((*yyd++ = *yys++) != '\0')
    continue;

  return yyd - 1;
}
#  endif
# endif

# ifndef yytnamerr
/* Copy to YYRES the contents of YYSTR after stripping away unnecessary
   quotes and backslashes, so that it's suitable for yyerror.  The
   heuristic is that double-quoting is unnecessary unless the string
   contains an apostrophe, a comma, or backslash (other than
   backslash-backslash).  YYSTR is taken from yytname.  If YYRES is
   null, do not copy; instead, return the length of what the result
   would have been.  */
static YYSIZE_T
yytnamerr (char *yyres, const char *yystr)
{
  if (*yystr == '"')
    {
      YYSIZE_T yyn = 0;
      char const *yyp = yystr;

      for (;;)
        switch (*++yyp)
          {
          case '\'':
          case ',':
            goto do_not_strip_quotes;

          case '\\':
            if (*++yyp != '\\')
              goto do_not_strip_quotes;
            /* Fall through.  */
          default:
            if (yyres)
              yyres[yyn] = *yyp;
            yyn++;
            break;

          case '"':
            if (yyres)
              yyres[yyn] = '\0';
            return yyn;
          }
    do_not_strip_quotes: ;
    }

  if (! yyres)
    return yystrlen (yystr);

  return yystpcpy (yyres, yystr) - yyres;
}
# endif

/* Copy into *YYMSG, which is of size *YYMSG_ALLOC, an error message
   about the unexpected token YYTOKEN for the state stack whose top is
   YYSSP.

   Return 0 if *YYMSG was successfully written.  Return 1 if *YYMSG is
   not large enough to hold the message.  In that case, also set
   *YYMSG_ALLOC to the required number of bytes.  Return 2 if the
   required number of bytes is too large to store.  */
static int
yysyntax_error (YYSIZE_T *yymsg_alloc, char **yymsg,
                yytype_int16 *yyssp, int yytoken)
{
  YYSIZE_T yysize0 = yytnamerr (YY_NULLPTR, yytname[yytoken]);
  YYSIZE_T yysize = yysize0;
  enum { YYERROR_VERBOSE_ARGS_MAXIMUM = 5 };
  /* Internationalized format string. */
  const char *yyformat = YY_NULLPTR;
  /* Arguments of yyformat. */
  char const *yyarg[YYERROR_VERBOSE_ARGS_MAXIMUM];
  /* Number of reported tokens (one for the "unexpected", one per
     "expected"). */
  int yycount = 0;

  /* There are many possibilities here to consider:
     - If this state is a consistent state with a default action, then
       the only way this function was invoked is if the default action
       is an error action.  In that case, don't check for expected
       tokens because there are none.
     - The only way there can be no lookahead present (in yychar) is if
       this state is a consistent state with a default action.  Thus,
       detecting the absence of a lookahead is sufficient to determine
       that there is no unexpected or expected token to report.  In that
       case, just report a simple "syntax error".
     - Don't assume there isn't a lookahead just because this state is a
       consistent state with a default action.  There might have been a
       previous inconsistent state, consistent state with a non-default
       action, or user semantic action that manipulated yychar.
     - Of course, the expected token list depends on states to have
       correct lookahead information, and it depends on the parser not
       to perform extra reductions after fetching a lookahead from the
       scanner and before detecting a syntax error.  Thus, state merging
       (from LALR or IELR) and default reductions corrupt the expected
       token list.  However, the list is correct for canonical LR with
       one exception: it will still contain any token that will not be
       accepted due to an error action in a later state.
  */
  if (yytoken != YYEMPTY)
    {
      int yyn = yypact[*yyssp];
      yyarg[yycount++] = yytname[yytoken];
      if (!yypact_value_is_default (yyn))
        {
          /* Start YYX at -YYN if negative to avoid negative indexes in
             YYCHECK.  In other words, skip the first -YYN actions for
             this state because they are default actions.  */
          int yyxbegin = yyn < 0 ? -yyn : 0;
          /* Stay within bounds of both yycheck and yytname.  */
          int yychecklim = YYLAST - yyn + 1;
          int yyxend = yychecklim < YYNTOKENS ? yychecklim : YYNTOKENS;
          int yyx;

          for (yyx = yyxbegin; yyx < yyxend; ++yyx)
            if (yycheck[yyx + yyn] == yyx && yyx != YYTERROR
                && !yytable_value_is_error (yytable[yyx + yyn]))
              {
                if (yycount == YYERROR_VERBOSE_ARGS_MAXIMUM)
                  {
                    yycount = 1;
                    yysize = yysize0;
                    break;
                  }
                yyarg[yycount++] = yytname[yyx];
                {
                  YYSIZE_T yysize1 = yysize + yytnamerr (YY_NULLPTR, yytname[yyx]);
                  if (! (yysize <= yysize1
                         && yysize1 <= YYSTACK_ALLOC_MAXIMUM))
                    return 2;
                  yysize = yysize1;
                }
              }
        }
    }

  switch (yycount)
    {
# define YYCASE_(N, S)                      \
      case N:                               \
        yyformat = S;                       \
      break
      YYCASE_(0, YY_("syntax error"));
      YYCASE_(1, YY_("syntax error, unexpected %s"));
      YYCASE_(2, YY_("syntax error, unexpected %s, expecting %s"));
      YYCASE_(3, YY_("syntax error, unexpected %s, expecting %s or %s"));
      YYCASE_(4, YY_("syntax error, unexpected %s, expecting %s or %s or %s"));
      YYCASE_(5, YY_("syntax error, unexpected %s, expecting %s or %s or %s or %s"));
# undef YYCASE_
    }

  {
    YYSIZE_T yysize1 = yysize + yystrlen (yyformat);
    if (! (yysize <= yysize1 && yysize1 <= YYSTACK_ALLOC_MAXIMUM))
      return 2;
    yysize = yysize1;
  }

  if (*yymsg_alloc < yysize)
    {
      *yymsg_alloc = 2 * yysize;
      if (! (yysize <= *yymsg_alloc
             && *yymsg_alloc <= YYSTACK_ALLOC_MAXIMUM))
        *yymsg_alloc = YYSTACK_ALLOC_MAXIMUM;
      return 1;
    }

  /* Avoid sprintf, as that infringes on the user's name space.
     Don't have undefined behavior even if the translation
     produced a string with the wrong number of "%s"s.  */
  {
    char *yyp = *yymsg;
    int yyi = 0;
    while ((*yyp = *yyformat) != '\0')
      if (*yyp == '%' && yyformat[1] == 's' && yyi < yycount)
        {
          yyp += yytnamerr (yyp, yyarg[yyi++]);
          yyformat += 2;
        }
      else
        {
          yyp++;
          yyformat++;
        }
  }
  return 0;
}
#endif /* YYERROR_VERBOSE */

/*-----------------------------------------------.
| Release the memory associated to this symbol.  |
`-----------------------------------------------*/

static void
yydestruct (const char *yymsg, int yytype, YYSTYPE *yyvaluep)
{
  YYUSE (yyvaluep);
  if (!yymsg)
    yymsg = "Deleting";
  YY_SYMBOL_PRINT (yymsg, yytype, yyvaluep, yylocationp);

  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  YYUSE (yytype);
  YY_IGNORE_MAYBE_UNINITIALIZED_END
}




/* The lookahead symbol.  */
int yychar;

/* The semantic value of the lookahead symbol.  */
YYSTYPE yylval;
/* Number of syntax errors so far.  */
int yynerrs;


/*----------.
| yyparse.  |
`----------*/

int
yyparse (void)
{
    int yystate;
    /* Number of tokens to shift before error messages enabled.  */
    int yyerrstatus;

    /* The stacks and their tools:
       'yyss': related to states.
       'yyvs': related to semantic values.

       Refer to the stacks through separate pointers, to allow yyoverflow
       to reallocate them elsewhere.  */

    /* The state stack.  */
    yytype_int16 yyssa[YYINITDEPTH];
    yytype_int16 *yyss;
    yytype_int16 *yyssp;

    /* The semantic value stack.  */
    YYSTYPE yyvsa[YYINITDEPTH];
    YYSTYPE *yyvs;
    YYSTYPE *yyvsp;

    YYSIZE_T yystacksize;

  int yyn;
  int yyresult;
  /* Lookahead token as an internal (translated) token number.  */
  int yytoken = 0;
  /* The variables used to return semantic value and location from the
     action routines.  */
  YYSTYPE yyval;

#if YYERROR_VERBOSE
  /* Buffer for error messages, and its allocated size.  */
  char yymsgbuf[128];
  char *yymsg = yymsgbuf;
  YYSIZE_T yymsg_alloc = sizeof yymsgbuf;
#endif

#define YYPOPSTACK(N)   (yyvsp -= (N), yyssp -= (N))

  /* The number of symbols on the RHS of the reduced rule.
     Keep to zero when no symbol should be popped.  */
  int yylen = 0;

  yyssp = yyss = yyssa;
  yyvsp = yyvs = yyvsa;
  yystacksize = YYINITDEPTH;

  YYDPRINTF ((stderr, "Starting parse\n"));

  yystate = 0;
  yyerrstatus = 0;
  yynerrs = 0;
  yychar = YYEMPTY; /* Cause a token to be read.  */
  goto yysetstate;

/*------------------------------------------------------------.
| yynewstate -- Push a new state, which is found in yystate.  |
`------------------------------------------------------------*/
 yynewstate:
  /* In all cases, when you get here, the value and location stacks
     have just been pushed.  So pushing a state here evens the stacks.  */
  yyssp++;

 yysetstate:
  *yyssp = yystate;

  if (yyss + yystacksize - 1 <= yyssp)
    {
      /* Get the current used size of the three stacks, in elements.  */
      YYSIZE_T yysize = yyssp - yyss + 1;

#ifdef yyoverflow
      {
        /* Give user a chance to reallocate the stack.  Use copies of
           these so that the &'s don't force the real ones into
           memory.  */
        YYSTYPE *yyvs1 = yyvs;
        yytype_int16 *yyss1 = yyss;

        /* Each stack pointer address is followed by the size of the
           data in use in that stack, in bytes.  This used to be a
           conditional around just the two extra args, but that might
           be undefined if yyoverflow is a macro.  */
        yyoverflow (YY_("memory exhausted"),
                    &yyss1, yysize * sizeof (*yyssp),
                    &yyvs1, yysize * sizeof (*yyvsp),
                    &yystacksize);

        yyss = yyss1;
        yyvs = yyvs1;
      }
#else /* no yyoverflow */
# ifndef YYSTACK_RELOCATE
      goto yyexhaustedlab;
# else
      /* Extend the stack our own way.  */
      if (YYMAXDEPTH <= yystacksize)
        goto yyexhaustedlab;
      yystacksize *= 2;
      if (YYMAXDEPTH < yystacksize)
        yystacksize = YYMAXDEPTH;

      {
        yytype_int16 *yyss1 = yyss;
        union yyalloc *yyptr =
          (union yyalloc *) YYSTACK_ALLOC (YYSTACK_BYTES (yystacksize));
        if (! yyptr)
          goto yyexhaustedlab;
        YYSTACK_RELOCATE (yyss_alloc, yyss);
        YYSTACK_RELOCATE (yyvs_alloc, yyvs);
#  undef YYSTACK_RELOCATE
        if (yyss1 != yyssa)
          YYSTACK_FREE (yyss1);
      }
# endif
#endif /* no yyoverflow */

      yyssp = yyss + yysize - 1;
      yyvsp = yyvs + yysize - 1;

      YYDPRINTF ((stderr, "Stack size increased to %lu\n",
                  (unsigned long int) yystacksize));

      if (yyss + yystacksize - 1 <= yyssp)
        YYABORT;
    }

  YYDPRINTF ((stderr, "Entering state %d\n", yystate));

  if (yystate == YYFINAL)
    YYACCEPT;

  goto yybackup;

/*-----------.
| yybackup.  |
`-----------*/
yybackup:

  /* Do appropriate processing given the current state.  Read a
     lookahead token if we need one and don't already have one.  */

  /* First try to decide what to do without reference to lookahead token.  */
  yyn = yypact[yystate];
  if (yypact_value_is_default (yyn))
    goto yydefault;

  /* Not known => get a lookahead token if don't already have one.  */

  /* YYCHAR is either YYEMPTY or YYEOF or a valid lookahead symbol.  */
  if (yychar == YYEMPTY)
    {
      YYDPRINTF ((stderr, "Reading a token: "));
      yychar = yylex ();
    }

  if (yychar <= YYEOF)
    {
      yychar = yytoken = YYEOF;
      YYDPRINTF ((stderr, "Now at end of input.\n"));
    }
  else
    {
      yytoken = YYTRANSLATE (yychar);
      YY_SYMBOL_PRINT ("Next token is", yytoken, &yylval, &yylloc);
    }

  /* If the proper action on seeing token YYTOKEN is to reduce or to
     detect an error, take that action.  */
  yyn += yytoken;
  if (yyn < 0 || YYLAST < yyn || yycheck[yyn] != yytoken)
    goto yydefault;
  yyn = yytable[yyn];
  if (yyn <= 0)
    {
      if (yytable_value_is_error (yyn))
        goto yyerrlab;
      yyn = -yyn;
      goto yyreduce;
    }

  /* Count tokens shifted since error; after three, turn off error
     status.  */
  if (yyerrstatus)
    yyerrstatus--;

  /* Shift the lookahead token.  */
  YY_SYMBOL_PRINT ("Shifting", yytoken, &yylval, &yylloc);

  /* Discard the shifted token.  */
  yychar = YYEMPTY;

  yystate = yyn;
  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  *++yyvsp = yylval;
  YY_IGNORE_MAYBE_UNINITIALIZED_END

  goto yynewstate;


/*-----------------------------------------------------------.
| yydefault -- do the default action for the current state.  |
`-----------------------------------------------------------*/
yydefault:
  yyn = yydefact[yystate];
  if (yyn == 0)
    goto yyerrlab;
  goto yyreduce;


/*-----------------------------.
| yyreduce -- Do a reduction.  |
`-----------------------------*/
yyreduce:
  /* yyn is the number of a rule to reduce with.  */
  yylen = yyr2[yyn];

  /* If YYLEN is nonzero, implement the default value of the action:
     '$$ = $1'.

     Otherwise, the following line sets YYVAL to garbage.
     This behavior is undocumented and Bison
     users should not rely upon it.  Assigning to YYVAL
     unconditionally makes the parser a bit smaller, and it avoids a
     GCC warning that YYVAL may be used uninitialized.  */
  yyval = yyvsp[1-yylen];


  YY_REDUCE_PRINT (yyn);
  switch (yyn)
    {
        case 5:
#line 120 "parser.y" /* yacc.c:1646  */
    {
                symbol_exprt proc(to_symbol_expr(stack((yyvsp[-14]))));
                code_typet ct;
                forall_operands(it, stack((yyvsp[-12])))
                {
                  symbol_exprt s(to_symbol_expr(*it));
                  code_typet::parametert p;
                  p.set_identifier(s.get_identifier());
                  ct.parameters().push_back(p);
                }
                proc.type().swap(ct);

                symbol_exprt rv(to_symbol_expr(stack((yyvsp[-9]))));
                symbol_exprt rl(to_symbol_expr(stack((yyvsp[-7]))));

                symbol_exprt tv(to_symbol_expr(stack((yyvsp[-5]))));
                symbol_exprt tl(to_symbol_expr(stack((yyvsp[-3]))));

                jsil_declarationt decl;
                decl.add_declarator(proc);
                decl.add_returns(rv.get_identifier(), rl.get_identifier());
                decl.add_throws(tv.get_identifier(), tl.get_identifier());
                if(stack((yyvsp[-1])).is_not_nil())
                  decl.add_value(to_code_block(to_code(stack((yyvsp[-1])))));

                PARSER.parse_tree.items.push_back(decl);
              }
#line 1662 "jsil_y.tab.cpp" /* yacc.c:1646  */
    break;

  case 7:
#line 151 "parser.y" /* yacc.c:1646  */
    {
            symbol_exprt e("eval");
            newstack((yyval)).swap(e);
          }
#line 1671 "jsil_y.tab.cpp" /* yacc.c:1646  */
    break;

  case 8:
#line 156 "parser.y" /* yacc.c:1646  */
    {
            stack((yyval)).set("proc_type", "builtin");
          }
#line 1679 "jsil_y.tab.cpp" /* yacc.c:1646  */
    break;

  case 9:
#line 160 "parser.y" /* yacc.c:1646  */
    {
            stack((yyval)).set("proc_type", "spec");
          }
#line 1687 "jsil_y.tab.cpp" /* yacc.c:1646  */
    break;

  case 11:
#line 167 "parser.y" /* yacc.c:1646  */
    {
                 symbol_exprt s(to_string_constant(stack((yyval))).get_value());
                 stack((yyval)).swap(s);
               }
#line 1696 "jsil_y.tab.cpp" /* yacc.c:1646  */
    break;

  case 12:
#line 174 "parser.y" /* yacc.c:1646  */
    {
                newstack((yyval));
              }
#line 1704 "jsil_y.tab.cpp" /* yacc.c:1646  */
    break;

  case 14:
#line 181 "parser.y" /* yacc.c:1646  */
    {
            newstack((yyval)).id(ID_parameters);
            stack((yyval)).move_to_operands(stack((yyvsp[0])));
          }
#line 1713 "jsil_y.tab.cpp" /* yacc.c:1646  */
    break;

  case 15:
#line 186 "parser.y" /* yacc.c:1646  */
    {
            (yyval)=(yyvsp[-2]);
            stack((yyval)).move_to_operands(stack((yyvsp[0])));
          }
#line 1722 "jsil_y.tab.cpp" /* yacc.c:1646  */
    break;

  case 16:
#line 193 "parser.y" /* yacc.c:1646  */
    {
                newstack((yyval));
              }
#line 1730 "jsil_y.tab.cpp" /* yacc.c:1646  */
    break;

  case 18:
#line 200 "parser.y" /* yacc.c:1646  */
    {
            newstack((yyval)).id(ID_code);
            to_code(stack((yyval))).set_statement(ID_block);
            stack((yyval)).move_to_operands(stack((yyvsp[0])));
          }
#line 1740 "jsil_y.tab.cpp" /* yacc.c:1646  */
    break;

  case 19:
#line 206 "parser.y" /* yacc.c:1646  */
    {
            (yyval)=(yyvsp[-1]);
            stack((yyval)).move_to_operands(stack((yyvsp[0])));
          }
#line 1749 "jsil_y.tab.cpp" /* yacc.c:1646  */
    break;

  case 20:
#line 213 "parser.y" /* yacc.c:1646  */
    {
           newstack((yyval))=code_skipt();
         }
#line 1757 "jsil_y.tab.cpp" /* yacc.c:1646  */
    break;

  case 21:
#line 217 "parser.y" /* yacc.c:1646  */
    {
           (yyval)=(yyvsp[-1]);
         }
#line 1765 "jsil_y.tab.cpp" /* yacc.c:1646  */
    break;

  case 22:
#line 223 "parser.y" /* yacc.c:1646  */
    {
             code_labelt l(
               to_symbol_expr(stack((yyvsp[0]))).get_identifier(),
               code_skipt());
             newstack((yyval)).swap(l);
           }
#line 1776 "jsil_y.tab.cpp" /* yacc.c:1646  */
    break;

  case 23:
#line 230 "parser.y" /* yacc.c:1646  */
    {
             code_gotot g(to_symbol_expr(stack((yyvsp[0]))).get_identifier());
             newstack((yyval)).swap(g);
           }
#line 1785 "jsil_y.tab.cpp" /* yacc.c:1646  */
    break;

  case 24:
#line 235 "parser.y" /* yacc.c:1646  */
    {
             code_gotot lt(to_symbol_expr(stack((yyvsp[-2]))).get_identifier());
             code_gotot lf(to_symbol_expr(stack((yyvsp[0]))).get_identifier());

             code_ifthenelset ite;
             ite.cond().swap(stack((yyvsp[-4])));
             ite.then_case().swap(lt);
             ite.else_case().swap(lf);

             newstack((yyval)).swap(ite);
           }
#line 1801 "jsil_y.tab.cpp" /* yacc.c:1646  */
    break;

  case 25:
#line 247 "parser.y" /* yacc.c:1646  */
    {
             newstack((yyval))=code_skipt();
           }
#line 1809 "jsil_y.tab.cpp" /* yacc.c:1646  */
    break;

  case 26:
#line 251 "parser.y" /* yacc.c:1646  */
    {
             code_assignt a(stack((yyvsp[-2])), stack((yyvsp[0])));
             newstack((yyval)).swap(a);
           }
#line 1818 "jsil_y.tab.cpp" /* yacc.c:1646  */
    break;

  case 27:
#line 256 "parser.y" /* yacc.c:1646  */
    {
             index_exprt i(stack((yyvsp[-5])), stack((yyvsp[-3])));
             code_assignt a(i, stack((yyvsp[0])));
             newstack((yyval)).swap(a);
           }
#line 1828 "jsil_y.tab.cpp" /* yacc.c:1646  */
    break;

  case 29:
#line 265 "parser.y" /* yacc.c:1646  */
    {
     side_effect_expr_function_callt f;
     f.function().swap(stack((yyvsp[-4])));
     if(stack((yyvsp[-2])).is_not_nil())
       f.arguments().swap(stack((yyvsp[-2])).operands());

     newstack((yyval)).swap(f);

     if(stack((yyvsp[0])).is_not_nil())
     {
       with_exprt w(stack((yyval)), stack((yyvsp[0])), nil_exprt());
       stack((yyval)).swap(w);
     }
   }
#line 1847 "jsil_y.tab.cpp" /* yacc.c:1646  */
    break;

  case 30:
#line 280 "parser.y" /* yacc.c:1646  */
    {
     exprt n("new");
     newstack((yyval)).swap(n);
   }
#line 1856 "jsil_y.tab.cpp" /* yacc.c:1646  */
    break;

  case 31:
#line 285 "parser.y" /* yacc.c:1646  */
    {
     exprt has_field("hasField");
     has_field.move_to_operands(stack((yyvsp[-3])));
     has_field.move_to_operands(stack((yyvsp[-1])));

     newstack((yyval)).swap(has_field);
   }
#line 1868 "jsil_y.tab.cpp" /* yacc.c:1646  */
    break;

  case 32:
#line 293 "parser.y" /* yacc.c:1646  */
    {
     index_exprt i(stack((yyvsp[-3])), stack((yyvsp[-1])));
     newstack((yyval)).swap(i);
   }
#line 1877 "jsil_y.tab.cpp" /* yacc.c:1646  */
    break;

  case 33:
#line 298 "parser.y" /* yacc.c:1646  */
    {
     exprt d("delete");
     d.move_to_operands(stack((yyvsp[-3])));
     d.move_to_operands(stack((yyvsp[-1])));

     newstack((yyval)).swap(d);
   }
#line 1889 "jsil_y.tab.cpp" /* yacc.c:1646  */
    break;

  case 34:
#line 306 "parser.y" /* yacc.c:1646  */
    {
     exprt proto_field("protoField");
     proto_field.move_to_operands(stack((yyvsp[-3])));
     proto_field.move_to_operands(stack((yyvsp[-1])));

     newstack((yyval)).swap(proto_field);
   }
#line 1901 "jsil_y.tab.cpp" /* yacc.c:1646  */
    break;

  case 35:
#line 314 "parser.y" /* yacc.c:1646  */
    {
     exprt proto_obj("protoObj");
     proto_obj.move_to_operands(stack((yyvsp[-3])));
     proto_obj.move_to_operands(stack((yyvsp[-1])));

     newstack((yyval)).swap(proto_obj);
   }
#line 1913 "jsil_y.tab.cpp" /* yacc.c:1646  */
    break;

  case 36:
#line 324 "parser.y" /* yacc.c:1646  */
    {
          newstack((yyval));
        }
#line 1921 "jsil_y.tab.cpp" /* yacc.c:1646  */
    break;

  case 37:
#line 328 "parser.y" /* yacc.c:1646  */
    {
          (yyval)=(yyvsp[0]);
        }
#line 1929 "jsil_y.tab.cpp" /* yacc.c:1646  */
    break;

  case 38:
#line 334 "parser.y" /* yacc.c:1646  */
    {
                 newstack((yyval));
               }
#line 1937 "jsil_y.tab.cpp" /* yacc.c:1646  */
    break;

  case 40:
#line 341 "parser.y" /* yacc.c:1646  */
    {
             newstack((yyval)).id(ID_expression_list);
             stack((yyval)).move_to_operands(stack((yyvsp[0])));
           }
#line 1946 "jsil_y.tab.cpp" /* yacc.c:1646  */
    break;

  case 41:
#line 346 "parser.y" /* yacc.c:1646  */
    {
             (yyval)=(yyvsp[-2]);
             stack((yyval)).move_to_operands(stack((yyvsp[0])));
           }
#line 1955 "jsil_y.tab.cpp" /* yacc.c:1646  */
    break;

  case 43:
#line 354 "parser.y" /* yacc.c:1646  */
    {
            (yyval)=(yyvsp[-1]);
            stack((yyval)).move_to_operands(stack((yyvsp[-2])));
            stack((yyval)).move_to_operands(stack((yyvsp[0])));
          }
#line 1965 "jsil_y.tab.cpp" /* yacc.c:1646  */
    break;

  case 45:
#line 363 "parser.y" /* yacc.c:1646  */
    {
                 (yyval)=(yyvsp[-1]);
                 stack((yyval)).move_to_operands(stack((yyvsp[0])));
               }
#line 1974 "jsil_y.tab.cpp" /* yacc.c:1646  */
    break;

  case 46:
#line 368 "parser.y" /* yacc.c:1646  */
    {
                 (yyval)=(yyvsp[-1]);
               }
#line 1982 "jsil_y.tab.cpp" /* yacc.c:1646  */
    break;

  case 47:
#line 372 "parser.y" /* yacc.c:1646  */
    {
                 exprt ref("ref");
                 ref.move_to_operands(stack((yyvsp[-5])));
                 ref.move_to_operands(stack((yyvsp[-3])));
                 ref.move_to_operands(stack((yyvsp[-1])));

                 newstack((yyval)).swap(ref);
               }
#line 1995 "jsil_y.tab.cpp" /* yacc.c:1646  */
    break;

  case 48:
#line 381 "parser.y" /* yacc.c:1646  */
    {
                 exprt field("field");
                 field.move_to_operands(stack((yyvsp[-1])));

                 newstack((yyval)).swap(field);
               }
#line 2006 "jsil_y.tab.cpp" /* yacc.c:1646  */
    break;

  case 49:
#line 388 "parser.y" /* yacc.c:1646  */
    {
                 exprt base(ID_base);
                 base.move_to_operands(stack((yyvsp[-1])));

                 newstack((yyval)).swap(base);
               }
#line 2017 "jsil_y.tab.cpp" /* yacc.c:1646  */
    break;

  case 50:
#line 395 "parser.y" /* yacc.c:1646  */
    {
                 exprt typeof_expr(ID_typeof);
                 typeof_expr.move_to_operands(stack((yyvsp[-1])));

                 newstack((yyval)).swap(typeof_expr);
               }
#line 2028 "jsil_y.tab.cpp" /* yacc.c:1646  */
    break;

  case 52:
#line 405 "parser.y" /* yacc.c:1646  */
    {
         newstack((yyval)).id(ID_null);
       }
#line 2036 "jsil_y.tab.cpp" /* yacc.c:1646  */
    break;

  case 53:
#line 409 "parser.y" /* yacc.c:1646  */
    {
         newstack((yyval)).id("undefined");
       }
#line 2044 "jsil_y.tab.cpp" /* yacc.c:1646  */
    break;

  case 54:
#line 413 "parser.y" /* yacc.c:1646  */
    {
         newstack((yyval)).id(ID_empty);
       }
#line 2052 "jsil_y.tab.cpp" /* yacc.c:1646  */
    break;

  case 55:
#line 417 "parser.y" /* yacc.c:1646  */
    {
         newstack((yyval)).make_true();
       }
#line 2060 "jsil_y.tab.cpp" /* yacc.c:1646  */
    break;

  case 56:
#line 421 "parser.y" /* yacc.c:1646  */
    {
         newstack((yyval)).make_false();
       }
#line 2068 "jsil_y.tab.cpp" /* yacc.c:1646  */
    break;

  case 58:
#line 426 "parser.y" /* yacc.c:1646  */
    {
         constant_exprt c(to_string_constant(stack((yyval)))
           .get_value(), string_typet());
         stack((yyval)).swap(c);
       }
#line 2078 "jsil_y.tab.cpp" /* yacc.c:1646  */
    break;

  case 62:
#line 437 "parser.y" /* yacc.c:1646  */
    {
               newstack((yyval)).id("proto");
             }
#line 2086 "jsil_y.tab.cpp" /* yacc.c:1646  */
    break;

  case 63:
#line 441 "parser.y" /* yacc.c:1646  */
    {
               newstack((yyval)).id("fid");
             }
#line 2094 "jsil_y.tab.cpp" /* yacc.c:1646  */
    break;

  case 64:
#line 445 "parser.y" /* yacc.c:1646  */
    {
               newstack((yyval)).id("scope");
             }
#line 2102 "jsil_y.tab.cpp" /* yacc.c:1646  */
    break;

  case 65:
#line 449 "parser.y" /* yacc.c:1646  */
    {
               newstack((yyval)).id("constructid");
             }
#line 2110 "jsil_y.tab.cpp" /* yacc.c:1646  */
    break;

  case 66:
#line 453 "parser.y" /* yacc.c:1646  */
    {
               newstack((yyval)).id("primvalue");
             }
#line 2118 "jsil_y.tab.cpp" /* yacc.c:1646  */
    break;

  case 67:
#line 457 "parser.y" /* yacc.c:1646  */
    {
               newstack((yyval)).id("targetfunction");
             }
#line 2126 "jsil_y.tab.cpp" /* yacc.c:1646  */
    break;

  case 68:
#line 461 "parser.y" /* yacc.c:1646  */
    {
               newstack((yyval)).id(ID_class);
             }
#line 2134 "jsil_y.tab.cpp" /* yacc.c:1646  */
    break;

  case 73:
#line 473 "parser.y" /* yacc.c:1646  */
    {
            newstack((yyval)).id(ID_equal);
          }
#line 2142 "jsil_y.tab.cpp" /* yacc.c:1646  */
    break;

  case 74:
#line 477 "parser.y" /* yacc.c:1646  */
    {
            newstack((yyval)).id(ID_lt);
          }
#line 2150 "jsil_y.tab.cpp" /* yacc.c:1646  */
    break;

  case 75:
#line 481 "parser.y" /* yacc.c:1646  */
    {
            newstack((yyval)).id(ID_le);
          }
#line 2158 "jsil_y.tab.cpp" /* yacc.c:1646  */
    break;

  case 76:
#line 487 "parser.y" /* yacc.c:1646  */
    {
               newstack((yyval)).id(ID_plus);
             }
#line 2166 "jsil_y.tab.cpp" /* yacc.c:1646  */
    break;

  case 77:
#line 491 "parser.y" /* yacc.c:1646  */
    {
               newstack((yyval)).id(ID_minus);
             }
#line 2174 "jsil_y.tab.cpp" /* yacc.c:1646  */
    break;

  case 78:
#line 495 "parser.y" /* yacc.c:1646  */
    {
               newstack((yyval)).id(ID_mult);
             }
#line 2182 "jsil_y.tab.cpp" /* yacc.c:1646  */
    break;

  case 79:
#line 499 "parser.y" /* yacc.c:1646  */
    {
               newstack((yyval)).id(ID_div);
             }
#line 2190 "jsil_y.tab.cpp" /* yacc.c:1646  */
    break;

  case 80:
#line 503 "parser.y" /* yacc.c:1646  */
    {
               newstack((yyval)).id(ID_mod);
             }
#line 2198 "jsil_y.tab.cpp" /* yacc.c:1646  */
    break;

  case 81:
#line 509 "parser.y" /* yacc.c:1646  */
    {
            newstack((yyval)).id(ID_and);
          }
#line 2206 "jsil_y.tab.cpp" /* yacc.c:1646  */
    break;

  case 82:
#line 513 "parser.y" /* yacc.c:1646  */
    {
            newstack((yyval)).id(ID_or);
          }
#line 2214 "jsil_y.tab.cpp" /* yacc.c:1646  */
    break;

  case 83:
#line 517 "parser.y" /* yacc.c:1646  */
    {
            newstack((yyval)).id("subtype_of");
          }
#line 2222 "jsil_y.tab.cpp" /* yacc.c:1646  */
    break;

  case 84:
#line 521 "parser.y" /* yacc.c:1646  */
    {
            newstack((yyval)).id(ID_concatenation);
          }
#line 2230 "jsil_y.tab.cpp" /* yacc.c:1646  */
    break;

  case 85:
#line 527 "parser.y" /* yacc.c:1646  */
    {
            newstack((yyval)).id(ID_bitand);
          }
#line 2238 "jsil_y.tab.cpp" /* yacc.c:1646  */
    break;

  case 86:
#line 531 "parser.y" /* yacc.c:1646  */
    {
            newstack((yyval)).id(ID_bitor);
          }
#line 2246 "jsil_y.tab.cpp" /* yacc.c:1646  */
    break;

  case 87:
#line 535 "parser.y" /* yacc.c:1646  */
    {
            newstack((yyval)).id(ID_bitxor);
          }
#line 2254 "jsil_y.tab.cpp" /* yacc.c:1646  */
    break;

  case 88:
#line 539 "parser.y" /* yacc.c:1646  */
    {
            newstack((yyval)).id(ID_shl);
          }
#line 2262 "jsil_y.tab.cpp" /* yacc.c:1646  */
    break;

  case 89:
#line 543 "parser.y" /* yacc.c:1646  */
    {
            newstack((yyval)).id(ID_shr);
          }
#line 2270 "jsil_y.tab.cpp" /* yacc.c:1646  */
    break;

  case 90:
#line 547 "parser.y" /* yacc.c:1646  */
    {
            newstack((yyval)).id(ID_lshr);
          }
#line 2278 "jsil_y.tab.cpp" /* yacc.c:1646  */
    break;

  case 91:
#line 553 "parser.y" /* yacc.c:1646  */
    {
          newstack((yyval)).id(ID_not);
        }
#line 2286 "jsil_y.tab.cpp" /* yacc.c:1646  */
    break;

  case 92:
#line 557 "parser.y" /* yacc.c:1646  */
    {
          newstack((yyval)).id(ID_unary_minus);
        }
#line 2294 "jsil_y.tab.cpp" /* yacc.c:1646  */
    break;

  case 93:
#line 561 "parser.y" /* yacc.c:1646  */
    {
          newstack((yyval)).id("num_to_string");
        }
#line 2302 "jsil_y.tab.cpp" /* yacc.c:1646  */
    break;

  case 94:
#line 565 "parser.y" /* yacc.c:1646  */
    {
          newstack((yyval)).id("string_to_num");
        }
#line 2310 "jsil_y.tab.cpp" /* yacc.c:1646  */
    break;

  case 95:
#line 569 "parser.y" /* yacc.c:1646  */
    {
          newstack((yyval)).id("num_to_int32");
        }
#line 2318 "jsil_y.tab.cpp" /* yacc.c:1646  */
    break;

  case 96:
#line 573 "parser.y" /* yacc.c:1646  */
    {
          newstack((yyval)).id("num_to_uint32");
        }
#line 2326 "jsil_y.tab.cpp" /* yacc.c:1646  */
    break;

  case 97:
#line 577 "parser.y" /* yacc.c:1646  */
    {
          newstack((yyval)).id(ID_bitnot);
        }
#line 2334 "jsil_y.tab.cpp" /* yacc.c:1646  */
    break;

  case 98:
#line 583 "parser.y" /* yacc.c:1646  */
    {
           newstack((yyval)).id("null_type");
         }
#line 2342 "jsil_y.tab.cpp" /* yacc.c:1646  */
    break;

  case 99:
#line 587 "parser.y" /* yacc.c:1646  */
    {
           newstack((yyval)).id("undefined_type");
         }
#line 2350 "jsil_y.tab.cpp" /* yacc.c:1646  */
    break;

  case 100:
#line 591 "parser.y" /* yacc.c:1646  */
    {
           newstack((yyval)).id(ID_boolean);
         }
#line 2358 "jsil_y.tab.cpp" /* yacc.c:1646  */
    break;

  case 101:
#line 595 "parser.y" /* yacc.c:1646  */
    {
           newstack((yyval)).id(ID_string);
         }
#line 2366 "jsil_y.tab.cpp" /* yacc.c:1646  */
    break;

  case 102:
#line 599 "parser.y" /* yacc.c:1646  */
    {
           newstack((yyval)).id("number");
         }
#line 2374 "jsil_y.tab.cpp" /* yacc.c:1646  */
    break;

  case 103:
#line 603 "parser.y" /* yacc.c:1646  */
    {
           newstack((yyval)).id("builtin_object");
         }
#line 2382 "jsil_y.tab.cpp" /* yacc.c:1646  */
    break;

  case 104:
#line 607 "parser.y" /* yacc.c:1646  */
    {
           newstack((yyval)).id("user_object");
         }
#line 2390 "jsil_y.tab.cpp" /* yacc.c:1646  */
    break;

  case 105:
#line 611 "parser.y" /* yacc.c:1646  */
    {
           newstack((yyval)).id("object");
         }
#line 2398 "jsil_y.tab.cpp" /* yacc.c:1646  */
    break;

  case 107:
#line 616 "parser.y" /* yacc.c:1646  */
    {
           newstack((yyval)).id(ID_reference);
         }
#line 2406 "jsil_y.tab.cpp" /* yacc.c:1646  */
    break;

  case 108:
#line 622 "parser.y" /* yacc.c:1646  */
    {
          newstack((yyval)).id(ID_member);
        }
#line 2414 "jsil_y.tab.cpp" /* yacc.c:1646  */
    break;

  case 109:
#line 626 "parser.y" /* yacc.c:1646  */
    {
          newstack((yyval)).id("variable");
        }
#line 2422 "jsil_y.tab.cpp" /* yacc.c:1646  */
    break;


#line 2426 "jsil_y.tab.cpp" /* yacc.c:1646  */
      default: break;
    }
  /* User semantic actions sometimes alter yychar, and that requires
     that yytoken be updated with the new translation.  We take the
     approach of translating immediately before every use of yytoken.
     One alternative is translating here after every semantic action,
     but that translation would be missed if the semantic action invokes
     YYABORT, YYACCEPT, or YYERROR immediately after altering yychar or
     if it invokes YYBACKUP.  In the case of YYABORT or YYACCEPT, an
     incorrect destructor might then be invoked immediately.  In the
     case of YYERROR or YYBACKUP, subsequent parser actions might lead
     to an incorrect destructor call or verbose syntax error message
     before the lookahead is translated.  */
  YY_SYMBOL_PRINT ("-> $$ =", yyr1[yyn], &yyval, &yyloc);

  YYPOPSTACK (yylen);
  yylen = 0;
  YY_STACK_PRINT (yyss, yyssp);

  *++yyvsp = yyval;

  /* Now 'shift' the result of the reduction.  Determine what state
     that goes to, based on the state we popped back to and the rule
     number reduced by.  */

  yyn = yyr1[yyn];

  yystate = yypgoto[yyn - YYNTOKENS] + *yyssp;
  if (0 <= yystate && yystate <= YYLAST && yycheck[yystate] == *yyssp)
    yystate = yytable[yystate];
  else
    yystate = yydefgoto[yyn - YYNTOKENS];

  goto yynewstate;


/*--------------------------------------.
| yyerrlab -- here on detecting error.  |
`--------------------------------------*/
yyerrlab:
  /* Make sure we have latest lookahead translation.  See comments at
     user semantic actions for why this is necessary.  */
  yytoken = yychar == YYEMPTY ? YYEMPTY : YYTRANSLATE (yychar);

  /* If not already recovering from an error, report this error.  */
  if (!yyerrstatus)
    {
      ++yynerrs;
#if ! YYERROR_VERBOSE
      yyerror (YY_("syntax error"));
#else
# define YYSYNTAX_ERROR yysyntax_error (&yymsg_alloc, &yymsg, \
                                        yyssp, yytoken)
      {
        char const *yymsgp = YY_("syntax error");
        int yysyntax_error_status;
        yysyntax_error_status = YYSYNTAX_ERROR;
        if (yysyntax_error_status == 0)
          yymsgp = yymsg;
        else if (yysyntax_error_status == 1)
          {
            if (yymsg != yymsgbuf)
              YYSTACK_FREE (yymsg);
            yymsg = (char *) YYSTACK_ALLOC (yymsg_alloc);
            if (!yymsg)
              {
                yymsg = yymsgbuf;
                yymsg_alloc = sizeof yymsgbuf;
                yysyntax_error_status = 2;
              }
            else
              {
                yysyntax_error_status = YYSYNTAX_ERROR;
                yymsgp = yymsg;
              }
          }
        yyerror (yymsgp);
        if (yysyntax_error_status == 2)
          goto yyexhaustedlab;
      }
# undef YYSYNTAX_ERROR
#endif
    }



  if (yyerrstatus == 3)
    {
      /* If just tried and failed to reuse lookahead token after an
         error, discard it.  */

      if (yychar <= YYEOF)
        {
          /* Return failure if at end of input.  */
          if (yychar == YYEOF)
            YYABORT;
        }
      else
        {
          yydestruct ("Error: discarding",
                      yytoken, &yylval);
          yychar = YYEMPTY;
        }
    }

  /* Else will try to reuse lookahead token after shifting the error
     token.  */
  goto yyerrlab1;


/*---------------------------------------------------.
| yyerrorlab -- error raised explicitly by YYERROR.  |
`---------------------------------------------------*/
yyerrorlab:

  /* Pacify compilers like GCC when the user code never invokes
     YYERROR and the label yyerrorlab therefore never appears in user
     code.  */
  if (/*CONSTCOND*/ 0)
     goto yyerrorlab;

  /* Do not reclaim the symbols of the rule whose action triggered
     this YYERROR.  */
  YYPOPSTACK (yylen);
  yylen = 0;
  YY_STACK_PRINT (yyss, yyssp);
  yystate = *yyssp;
  goto yyerrlab1;


/*-------------------------------------------------------------.
| yyerrlab1 -- common code for both syntax error and YYERROR.  |
`-------------------------------------------------------------*/
yyerrlab1:
  yyerrstatus = 3;      /* Each real token shifted decrements this.  */

  for (;;)
    {
      yyn = yypact[yystate];
      if (!yypact_value_is_default (yyn))
        {
          yyn += YYTERROR;
          if (0 <= yyn && yyn <= YYLAST && yycheck[yyn] == YYTERROR)
            {
              yyn = yytable[yyn];
              if (0 < yyn)
                break;
            }
        }

      /* Pop the current state because it cannot handle the error token.  */
      if (yyssp == yyss)
        YYABORT;


      yydestruct ("Error: popping",
                  yystos[yystate], yyvsp);
      YYPOPSTACK (1);
      yystate = *yyssp;
      YY_STACK_PRINT (yyss, yyssp);
    }

  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  *++yyvsp = yylval;
  YY_IGNORE_MAYBE_UNINITIALIZED_END


  /* Shift the error token.  */
  YY_SYMBOL_PRINT ("Shifting", yystos[yyn], yyvsp, yylsp);

  yystate = yyn;
  goto yynewstate;


/*-------------------------------------.
| yyacceptlab -- YYACCEPT comes here.  |
`-------------------------------------*/
yyacceptlab:
  yyresult = 0;
  goto yyreturn;

/*-----------------------------------.
| yyabortlab -- YYABORT comes here.  |
`-----------------------------------*/
yyabortlab:
  yyresult = 1;
  goto yyreturn;

#if !defined yyoverflow || YYERROR_VERBOSE
/*-------------------------------------------------.
| yyexhaustedlab -- memory exhaustion comes here.  |
`-------------------------------------------------*/
yyexhaustedlab:
  yyerror (YY_("memory exhausted"));
  yyresult = 2;
  /* Fall through.  */
#endif

yyreturn:
  if (yychar != YYEMPTY)
    {
      /* Make sure we have latest lookahead translation.  See comments at
         user semantic actions for why this is necessary.  */
      yytoken = YYTRANSLATE (yychar);
      yydestruct ("Cleanup: discarding lookahead",
                  yytoken, &yylval);
    }
  /* Do not reclaim the symbols of the rule whose action triggered
     this YYABORT or YYACCEPT.  */
  YYPOPSTACK (yylen);
  YY_STACK_PRINT (yyss, yyssp);
  while (yyssp != yyss)
    {
      yydestruct ("Cleanup: popping",
                  yystos[*yyssp], yyvsp);
      YYPOPSTACK (1);
    }
#ifndef yyoverflow
  if (yyss != yyssa)
    YYSTACK_FREE (yyss);
#endif
#if YYERROR_VERBOSE
  if (yymsg != yymsgbuf)
    YYSTACK_FREE (yymsg);
#endif
  return yyresult;
}
#line 631 "parser.y" /* yacc.c:1906  */

