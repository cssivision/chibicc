#define _POSIX_C_SOURCE 200809L
#include "stdio.h"
#include "stdarg.h"
#include "stdlib.h"
#include "string.h"
#include "ctype.h"
#include "stdbool.h"
#include "assert.h"

typedef struct Type Type;
typedef struct Token Token;
typedef struct Obj Obj;
typedef struct Node Node;

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

    ND_RETURN,   // return
    ND_BLOCK,    // { .. }
    ND_IF,       // if
    ND_FOR,      // for or while
    ND_EXPR_STMT // Expression statement
} NodeKind;

// Local variable
struct Obj
{
    Obj *next;
    char *name; // Variable name
    Type *ty;
    int offset; // Offset from RBP
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

    // "if" or "for" statement
    Node *cond;
    Node *then;
    Node *els;
    Node *init;
    Node *inc;
};

typedef struct Function Function;
struct Function
{
    Function *next;
    char *name;
    Node *body;
    Obj *locals;
    int stack_size;
};

typedef enum
{
    TY_INT,
    TY_PTR,
    TY_FUNC,
} TypeKind;

struct Type
{
    TypeKind kind;
    Type *base;
    Type *return_ty;
    // Declaration
    Token *name;
};

bool is_integer(Type *ty);
void add_type(Node *node);
Type *pointer_to(Type *base);
Type *func_type(Type *return_ty);
extern Type *ty_int;

void error(char *fmt, ...);
void error_tok(Token *tok, char *fmt, ...);

bool equal(Token *tok, char *p);
bool consume(Token **rest, Token *tok, char *str);

Token *tokenize(char *p);
Function *parse(Token *tok);
void codegen(Function *prog);
