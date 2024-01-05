#define _POSIX_C_SOURCE 200809L
#include "stdio.h"
#include "stdarg.h"
#include "stdint.h"
#include "stdlib.h"
#include "string.h"
#include "libgen.h"
#include "strings.h"
#include "ctype.h"
#include "glob.h"
#include "errno.h"
#include "stdbool.h"
#include "assert.h"
#include "sys/types.h"
#include "sys/wait.h"
#include "unistd.h"
#include "sys/stat.h"
#include "time.h"

typedef struct
{
    char **data;
    int capacity;
    int len;
} StringArray;

void strarray_push(StringArray *arr, char *s);

#define MAX(x, y) ((x) < (y) ? (y) : (x))
#define MIN(x, y) ((x) < (y) ? (x) : (y))

typedef struct Type Type;
typedef struct Token Token;
typedef struct Obj Obj;
typedef struct Node Node;
typedef struct Member Member;
typedef struct Hideset Hideset;

typedef enum
{
    TK_PUNCT,
    TK_IDENT,
    TK_NUM,
    TK_PP_NUM, // Preprocessing numbers
    TK_KEYWORD,
    TK_EOF,
    TK_STR // "str"
} TokenKind;

typedef struct
{
    char *name;
    int file_no;
    char *contents;
} File;

struct Token
{
    TokenKind kind;
    Token *next;
    int64_t val;
    double fval;
    char *loc;
    int len;
    Type *ty;
    char *str;
    File *file;

    int line_no;      // Line number
    bool at_bol;      // True if this token is at beginning of line
    bool has_space;   // True if this token follows a space character
    Hideset *hideset; // For macro expansion
    Token *origin;    // If this is expanded from a macro, the original token
};

struct Member
{
    Member *next;
    Token *tok;
    Type *ty;
    Token *name;
    int idx;
    int offset;
    int align;

    // Bitfield
    bool is_bitfield;
    int bit_offset;
    int bit_width;
};

typedef enum
{
    ND_ADD,      // +
    ND_SUB,      // -
    ND_MUL,      // *
    ND_DIV,      // /
    ND_MOD,      // %
    ND_NEG,      // unary -
    ND_SHL,      // <<
    ND_SHR,      // >>
    ND_EQ,       // ==
    ND_NE,       // !=
    ND_LT,       // <
    ND_LE,       // <=
    ND_ASSIGN,   // =
    ND_ADDR,     // &
    ND_DEREF,    // *
    ND_NOT,      // !
    ND_BITNOT,   // ~
    ND_BITOR,    // |
    ND_BITXOR,   // ^
    ND_BITAND,   // &
    ND_LOGAND,   // &&
    ND_LOGOR,    // ||
    ND_COND,     // "?:"
    ND_NUM,      // Integer
    ND_VAR,      // Variable
    ND_FUNCCALL, // Function call
    ND_COMMA,    // ,
    ND_MEMBER,   // .
    ND_CAST,     // type cast
    ND_MEMZERO,  // Zero-clear a stack variable

    ND_SWITCH,    // switch
    ND_CASE,      // case
    ND_GOTO,      // goto
    ND_LABEL,     // label
    ND_RETURN,    // return
    ND_BLOCK,     // { .. }
    ND_IF,        // if
    ND_FOR,       // for or while
    ND_DO,        // do ... while
    ND_EXPR_STMT, // Expression statement
    ND_STMT_EXPR,
    ND_NULL_EXPR
} NodeKind;

// Global variable can be initialized either by a constant expression
// or a pointer to another global variable. This struct represents the
// latter.
typedef struct Relocation Relocation;
struct Relocation
{
    Relocation *next;
    int offset;
    char *label;
    long addend;
};

// Variable or function
struct Obj
{
    Obj *next;
    char *name; // Variable name
    Type *ty;
    int offset;    // Offset from RBP
    bool is_local; // local or global/function
    int align;     // alignment

    // Global variable or function
    bool is_function;
    bool is_definition;
    bool is_static;

    // Global variable
    char *init_data;
    Relocation *rel;

    // Function
    Node *body;
    Obj *params;
    Obj *va_area;
    Obj *locals;
    int stack_size;
};

struct Node
{
    NodeKind kind;
    Node *next;
    Type *ty;
    Token *tok; // Representative token
    Node *lhs;
    Node *rhs;

    // Goto or labeled statement
    char *label;
    char *unique_label;
    Node *goto_next;

    // "break" label
    char *brk_label;
    // "continue" lable
    char *cont_label;

    Node *body; // use if kind == ND_BLOCK

    // Function
    Node *args;
    bool pass_by_stack;
    Obj *ret_buffer;

    // Switch-cases
    Node *case_next;
    Node *default_case;

    // Variable
    Obj *var;

    // Numeric literal
    int64_t val;
    double fval;

    Member *member;

    // "if" or "for" statement
    Node *cond;
    Node *then;
    Node *els;
    Node *init;
    Node *inc;
};

typedef enum
{
    TY_INT,
    TY_PTR,
    TY_FUNC,
    TY_ARRAY,
    TY_CHAR,
    TY_VOID,
    TY_BOOL,
    TY_STRUCT,
    TY_UNION,
    TY_LONG,
    TY_FLOAT,
    TY_DOUBLE,
    TY_SHORT,
    TY_ENUM
} TypeKind;

struct Type
{
    TypeKind kind;

    int size; // sizeof() value
    int align;
    bool is_unsigned; // unsigned or signed

    // Pointer
    Type *base;

    // Declaration
    Token *name;
    Token *name_pos;

    // Array
    int array_len;

    // Function
    Type *return_ty;
    Type *params;
    bool is_variadic;
    Type *next;

    Member *members;
    bool is_flexible;
};

bool is_integer(Type *ty);
void add_type(Node *node);
Type *pointer_to(Type *base);
Type *func_type(Type *return_ty);
Node *new_cast(Node *lhs, Type *ty);
Type *copy_type(Type *ty);
Type *enum_type();
Type *struct_type();
Type *array_of(Type *base, int len);
extern Type *ty_int;
extern Type *ty_char;
extern Type *ty_long;
extern Type *ty_short;
extern Type *ty_void;
extern Type *ty_bool;
extern Type *ty_uchar;
extern Type *ty_ushort;
extern Type *ty_uint;
extern Type *ty_ulong;
extern Type *ty_float;
extern Type *ty_double;

void error(char *fmt, ...);
void error_tok(Token *tok, char *fmt, ...);
void error_at(char *loc, char *fmt, ...);
void warn_tok(Token *tok, char *fmt, ...);
bool is_flonum(Type *ty);
bool is_numeric(Type *ty);
bool file_exists(char *path);

bool equal(Token *tok, char *p);
bool consume(Token **rest, Token *tok, char *str);
int64_t const_expr(Token **rest, Token *tok);
Token *skip(Token *tok, char *op);

char *format(char *fmt, ...);

Token *tokenize_file(char *path);
Token *tokenize(File *file);
File *new_file(char *name, int file_no, char *contents);
Obj *parse(Token *tok);
void codegen(Obj *prog, FILE *out);
int align_to(int n, int align);
int align_down(int n, int align);
void convert_pp_tokens(Token *tok);
File **get_input_files(void);

#define unreachable() \
    error("internal error at %s:%d", __FILE__, __LINE__)

//
// preprocess.c
//

void init_macros(void);
void define_macro(char *name, char *buf);
void undef_macro(char *name);
Token *preprocess(Token *tok);

//
// unicode.c
//

int encode_utf8(char *buf, uint32_t c);
uint32_t decode_utf8(char **new_pos, char *p);

//
// main.c
//

extern char *base_file;
extern StringArray include_paths;