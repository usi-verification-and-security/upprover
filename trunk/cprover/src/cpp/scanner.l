%option nounput

%{

/*************** Includes and Defines *****************************/

#ifdef _WIN32
#define YY_NO_UNISTD_H
static int isatty(int) { return 0; }
#endif

#include <expr.h>
#include <arith_tools.h>
#include <config.h>

#include <ansi-c/c_types.h>
#include <ansi-c/preprocessor_line.h>

#include <ansi-c/literals/convert_float_literal.h>
#include <ansi-c/literals/convert_integer_literal.h>
#include <ansi-c/literals/unescape_string.h>
#include <ansi-c/literals/convert_character_literal.h>
#include <ansi-c/literals/convert_string_literal.h>

#define PARSER cpp_parser
#define YYSTYPE unsigned
#undef  ECHO
#define ECHO

#include "cpp_parser.h"
#include "tokens.h"

void set_line_no();

%}

%x COMMENT1
%x COMMENT2
%x GCC_ATTRIBUTE
%x MSC_ASM1
%x MSC_ASM2
%x MSC_DECLSPEC
%x MSC_PRAGMA
%x MSC_ANNOTATION

%{
void cpp_scanner_init()
{
  YY_FLUSH_BUFFER;
  BEGIN(0); // this is INITIAL, hopefully
}
%}

identifier [a-zA-Z_][0-9a-zA-Z_$]*

exponent_part [eE][-+]?[0-9]+
fractional_constant ([0-9]*"."[0-9]+)|([0-9]+".")
floating_constant (({fractional_constant}{exponent_part}?)|([0-9]+{exponent_part}))[FfLl]?

integer_suffix [uUlL]
integer_suffix_opt {integer_suffix}*
decimal_constant [1-9][0-9]*{integer_suffix_opt}
octal_constant "0"[0-7]*{integer_suffix_opt}
hex_constant "0"[xX][0-9a-fA-F]+{integer_suffix_opt}

simple_escape [abfnrtv'"?\\]
octal_escape  [0-7]{1,3}
hex_escape "x"[0-9a-fA-F]+

escape_sequence [\\]({simple_escape}|{octal_escape}|{hex_escape})
c_char [^'\\\n]|{escape_sequence}
s_char [^"\\\n]|{escape_sequence}

h_tab [\011]
form_feed [\014]
v_tab [\013]
c_return [\015]

horizontal_white [ ]|{h_tab}
ws {horizontal_white}*

integer         [0-9]+
cppfile         "\""[ !#-~]*"\""
cpplineno       "#"{horizontal_white}*"line"*{horizontal_white}*{integer}.*"\n"
pragma          "#"{horizontal_white}*pragma{horizontal_white}.*"\n"

%%

%{
#define loc() (PARSER.current_token().text=yytext,PARSER.set_location())
%}

<INITIAL>"/*"	{ BEGIN(COMMENT1); }	/* begin C comment state */

<COMMENT1>{
   "*/"		{ BEGIN(INITIAL); }	/* end comment state, back to INITIAL */
   "/*"		{ yycpperror("Probably nested comments"); }
   <<EOF>>	{ yycpperror("Unterminated comment"); }
   [^*/\n]*	{ /* ignore every char except '*' and NL (performance!) */ }
   .		{ } /* all single characters within comments are ignored */
   \n		{ } 
	}

<INITIAL>"//"	{ BEGIN(COMMENT2); }	/* begin C++ comment state */

<COMMENT2>{
   \n		{ BEGIN(INITIAL); }	/* end comment state, back to INITIAL */
   .*		{ } /* all characters within comments are ignored */
	}

<GCC_ATTRIBUTE>{
")"    { PARSER.parenthesis_counter--;
         if(PARSER.parenthesis_counter==0)
         BEGIN(INITIAL); }
"("    { PARSER.parenthesis_counter++; }
.      { /* Throw away */ }
}

"[repeatable" { BEGIN(MSC_ANNOTATION); }
"[source_annotation_attribute" { BEGIN(MSC_ANNOTATION); }
"[returnvalue"  { BEGIN(MSC_ANNOTATION); }
"[SA_Pre"       { BEGIN(MSC_ANNOTATION); }
"[SA_Post"      { BEGIN(MSC_ANNOTATION); }
"[SA_FormatString" { BEGIN(MSC_ANNOTATION); }

"__pragma"      { BEGIN(MSC_PRAGMA); PARSER.parenthesis_counter=0; }

<MSC_ANNOTATION>"]" { BEGIN(INITIAL); }
<MSC_ANNOTATION>. { /* ignore */ }

<MSC_ASM1>{ws}"{" { BEGIN(MSC_ASM2); loc(); return '{'; }
<MSC_ASM1>[^{^}]* { loc();
                    PARSER.current_token().data=exprt(yytext);
                    BEGIN(INITIAL);
                    return StringL; }

<MSC_ASM2>[^}]* { loc();
                  PARSER.current_token().data=exprt(yytext);
                  return StringL; }
<MSC_ASM2>"}"   { BEGIN(INITIAL); loc(); return '}'; }

<MSC_DECLSPEC>")"    { PARSER.parenthesis_counter--;
                        if(PARSER.parenthesis_counter==0)
                          BEGIN(INITIAL); }
<MSC_DECLSPEC>"("    { PARSER.parenthesis_counter++; }
<MSC_DECLSPEC>.      { /* Throw away */ }

<MSC_PRAGMA>")"    { PARSER.parenthesis_counter--;
                        if(PARSER.parenthesis_counter==0)
                          BEGIN(INITIAL); }
<MSC_PRAGMA>"("    { PARSER.parenthesis_counter++; }
<MSC_PRAGMA>.      { /* Throw away */ }

<INITIAL>{
{horizontal_white}+
({v_tab}|{c_return}|{form_feed})+
({horizontal_white}|{v_tab}|{c_return}|{form_feed})*"\n"

__alignof__         { loc(); return SIZEOF; }
__asm__|asm|__asm   { if(PARSER.mode==cpp_parsert::MSC)
                      {
                        BEGIN(MSC_ASM1);
                        return MSC_ASM;
                      }
                      else
                      {
                        loc();
                        return GCC_ASM;
                      }
                    }
__attribute         { BEGIN(GCC_ATTRIBUTE); PARSER.parenthesis_counter=0; }
__attribute__       { BEGIN(GCC_ATTRIBUTE); PARSER.parenthesis_counter=0; }
_cdecl		    { /* ignore */ }
__cdecl		    { /* ignore */ }
__const             { loc(); return CONST; }
__declspec          { BEGIN(MSC_DECLSPEC); PARSER.parenthesis_counter=0; }
__extension__       { loc(); return Ignore; }
_inline             { loc(); return INLINE; }
__inline            { loc(); return INLINE; }
__inline__          { loc(); return INLINE; }
__forceinline       { loc(); return PARSER.mode==cpp_parsert::MSC?INLINE:Identifier; }
__noreturn__        { loc(); return Ignore; }
restrict            { loc(); return Ignore; }
__restrict__        { loc(); return Ignore; }
__restrict          { loc(); return Ignore; }
__stdcall           { loc(); return PARSER.mode==cpp_parsert::MSC?Ignore:Identifier; }
__fastcall          { loc(); return PARSER.mode==cpp_parsert::MSC?Ignore:Identifier; }
__clrcall           { loc(); return PARSER.mode==cpp_parsert::MSC?Ignore:Identifier; }
__signed            { loc(); return SIGNED; }
__signed__          { loc(); return SIGNED; }
__vector            { loc(); return Ignore; }
__volatile__        { loc(); return VOLATILE; }
typeof              { loc(); return TYPEOF; }
__typeof            { loc(); return TYPEOF; }
__typeof__          { loc(); return TYPEOF; }
__int8              { loc(); return PARSER.mode==cpp_parsert::MSC?INT8:Identifier; }
__int16             { loc(); return PARSER.mode==cpp_parsert::MSC?INT16:Identifier; }
__int32             { loc(); return PARSER.mode==cpp_parsert::MSC?INT32:Identifier; }
__int64             { loc(); return PARSER.mode==cpp_parsert::MSC?INT64:Identifier; }
__ptr32             { loc(); return PARSER.mode==cpp_parsert::MSC?PTR32:Identifier; }
__ptr64             { loc(); return PARSER.mode==cpp_parsert::MSC?PTR64:Identifier; }
__thiscall          { loc(); return Ignore; }
__w64               { loc(); return Ignore; }
auto                { loc(); return AUTO; }
bool                { loc(); return BOOLEAN; }
break               { loc(); return BREAK; }
case                { loc(); return CASE; }
catch               { loc(); return CATCH; }
char                { loc(); return CHAR; }
class               { loc(); return CLASS; }
const               { loc(); return CONST; }
continue            { loc(); return CONTINUE; }
default             { loc(); return DEFAULT; }
delete              { loc(); return DELETE; }
do                  { loc(); return DO; }
double              { loc(); return DOUBLE; }
else                { loc(); return ELSE; }
enum                { loc(); return ENUM; }
explicit            { loc(); return EXPLICIT; }
extern              { loc(); return EXTERN; }
float               { loc(); return FLOAT; }
for                 { loc(); return FOR; }
friend              { loc(); return FRIEND; }
goto                { loc(); return GOTO; }
if                  { loc(); return IF; }
inline              { loc(); return INLINE; }
int                 { loc(); return INT; }
long                { loc(); return LONG; }
mutable             { loc(); return MUTABLE; }
namespace           { loc(); return NAMESPACE; }
new                 { loc(); return NEW; }
noreturn            { loc(); return Ignore; }
operator            { loc(); return OPERATOR; }
private             { loc(); return PRIVATE; }
protected           { loc(); return PROTECTED; }
public              { loc(); return PUBLIC; }
register            { loc(); return REGISTER; }
return              { loc(); return RETURN; }
short               { loc(); return SHORT; }
signed              { loc(); return SIGNED; }
sizeof              { loc(); return SIZEOF; }
static              { loc(); return STATIC; }
struct              { loc(); return STRUCT; }
switch              { loc(); return SWITCH; }
template            { loc(); return TEMPLATE; }
this                { loc(); return THIS; }
throw               { loc(); return THROW; }
try                 { loc(); return TRY; }
typedef             { loc(); return TYPEDEF; }
typeid              { loc(); return TYPEID; }
typename            { loc(); return TYPENAME; }
union               { loc(); return UNION; }
unsigned            { loc(); return UNSIGNED; }
using               { loc(); return USING; }
virtual             { loc(); return VIRTUAL; }
void                { loc(); return VOID; }
volatile            { loc(); return VOLATILE; }
wchar_t	            { loc(); return WCHAR_T; }
while               { loc(); return WHILE; }
__CPROVER_thread_local { loc(); return THREAD_LOCAL; }

{identifier}        { loc();
                      return Identifier; // or TYPDEFname
                    }

{decimal_constant}  { loc();
                      PARSER.current_token().data=convert_integer_literal(yytext, 10);
                      return Constant;
                    }

{octal_constant}    { loc();
                      PARSER.current_token().data=convert_integer_literal(yytext, 8);
                      return Constant;
                    }

{hex_constant}      { loc();
                      PARSER.current_token().data=convert_integer_literal(yytext, 16);
                      return Constant;
                    }

{floating_constant} {
                      loc();
                      PARSER.current_token().data=convert_float_literal(yytext);
                      return Constant;
                    }

"L"?[']{c_char}+['] { 
                      loc();
                      PARSER.current_token().data=convert_character_literal(yytext);
                      return Constant;
                    }

"L"?["]{s_char}*["] {
                      loc();
                      PARSER.current_token().data=convert_string_literal(yytext);
                      return StringL;
                    }

"("                 { loc(); return yytext[0]; }
")"                 { loc(); return yytext[0]; }
","                 { loc(); return yytext[0]; }

{cpplineno}         { set_line_no(); }
{pragma}            { /* ignore it */ }

"#"

"#".*"\n"           { yycpperror("unknown preprocessor directive"); }

"##"                { }

"{"                 { loc(); return '{'; }
"}"                 { loc(); return '}'; }
"["                 { loc(); return '['; }
"]"                 { loc(); return ']'; }
"."                 { loc(); return '.'; }
"&"                 { loc(); return '&'; }
"*"                 { loc(); return '*'; }
"+"                 { loc(); return '+'; }
"-"                 { loc(); return '-'; }
"~"                 { loc(); return '~'; }
"!"                 { loc(); return '!'; }
"/"                 { loc(); return '/'; }
"%"                 { loc(); return '%'; }
"<"                 { loc(); return '<'; }
">"                 { loc(); return '>'; }
"^"                 { loc(); return '^'; }
"|"                 { loc(); return '|'; }
"?"                 { loc(); return '?'; }
":"                 { loc(); return ':'; }
";"                 { loc(); return ';'; }
"="                 { loc(); return '='; }

".*"                { loc(); return PmOp; }
"->*"               { loc(); return PmOp; }
"::"                { loc(); return Scope; }
"->"                { loc(); return ArrowOp; }
"++"                { loc(); return IncOp; }
"--"                { loc(); return IncOp; }
"<<"                { loc(); return ShiftOp; }
">>"                { loc(); return ShiftOp; }
"<="                { loc(); return RelOp; }
">="                { loc(); return RelOp; }
"=="                { loc(); return EqualOp; }
"!="                { loc(); return EqualOp; }
"&&"                { loc(); return LogAndOp; }
"||"                { loc(); return LogOrOp; }
"*="                { loc(); return AssignOp; }
"/="                { loc(); return AssignOp; }
"%="                { loc(); return AssignOp; }
"+="                { loc(); return AssignOp; }
"-="                { loc(); return AssignOp; }
"<<="               { loc(); return AssignOp; }
">>="               { loc(); return AssignOp; }
"&="                { loc(); return AssignOp; }
"^="                { loc(); return AssignOp; }
"|="                { loc(); return AssignOp; }
"..."               { loc(); return Ellipsis; }

.                   { yycpperror("unknown character"); }
}

%%

int yywrap() { return 1; }

void set_line_no()
{
  preprocessor_line(yytext, PARSER.line_no, PARSER.filename);
}
