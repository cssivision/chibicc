#define _POSIX_C_SOURCE 200809L
#include "stdio.h"
#include "stdarg.h"
#include "stdlib.h"
#include "string.h"
#include "ctype.h"
#include "errno.h"
#include "stdbool.h"
#include "assert.h"

typedef struct Type Type;
typedef struct Token Token;
typedef struct Obj Obj;
typedef struct Node Node;
typedef struct Member Member;

typedef enum
{
    TK_PUNCT,
    TK_IDENT,
    TK_NUM,
    TK_KEYWORD,
    TK_EOF,
} TokenKind;

struct Token
{
    TokenKind kind;
    Token *next;
    int val;
    char *loc;
    int len;
    Type *ty;
    char *str;

    int line_no; // Line number
};

struct Member
{
    Member *next;
    Type *ty;
    Token *name;
    int offset;
};

typedef enum
{
    ND_ADD,      // +
    ND_SUB,      // -
    ND_MUL,      // *
    ND_DIV,      // /
    ND_NEG,      // unary -
    ND_EQ,       // ==
    ND_NE,       // !=
    ND_LT,       // <
    ND_LE,       // <=
    ND_ASSIGN,   // =
    ND_ADDR,     // &
    ND_DEREF,    // *
    ND_NUM,      // Integer
    ND_VAR,      // Variable
    ND_FUNCCALL, // Function call
    TK_STR,      // "str"
    ND_COMMA,    // ,
    ND_MEMBER,   // .

    ND_RETURN,    // return
    ND_BLOCK,     // { .. }
    ND_IF,        // if
    ND_FOR,       // for or while
    ND_EXPR_STMT, // Expression statement
    ND_STMT_EXPR
} NodeKind;

// Variable or function
struct Obj
{
    Obj *next;
    char *name; // Variable name
    Type *ty;
    int offset;    // Offset from RBP
    bool is_local; // local or global/function
    Node *body;
    // Function params
    Obj *params;

    // Global variable or function
    bool is_function;

    // Global variable
    char *init_data;

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

    Node *body; // use if kind == ND_BLOCK

    char *funcname;
    Node *args;

    int val; // Used if kind == ND_NUM

    Obj *var; // Used if kind == ND_VAR

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
    TY_STRUCT,
    TY_UNION
} TypeKind;

struct Type
{
    TypeKind kind;

    int size; // sizeof() value
    int align;

    // Pointer
    Type *base;

    // Declaration
    Token *name;

    // Array
    int array_len;

    // Function
    Type *return_ty;
    Type *params;
    Type *next;

    Member *members;
};

bool is_integer(Type *ty);
void add_type(Node *node);
Type *pointer_to(Type *base);
Type *func_type(Type *return_ty);
Type *copy_type(Type *ty);
Type *array_of(Type *base, int len);
extern Type *ty_int;
extern Type *ty_char;

void error(char *fmt, ...);
void error_tok(Token *tok, char *fmt, ...);

bool equal(Token *tok, char *p);
bool consume(Token **rest, Token *tok, char *str);

char *format(char *fmt, ...);

Token *tokenize_file(char *path);
Obj *parse(Token *tok);
void codegen(Obj *prog, FILE *out);
int align_to(int n, int align);
