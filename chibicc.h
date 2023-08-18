#define _POSIX_C_SOURCE 200809L
#include "stdio.h"
#include "stdarg.h"
#include "stdlib.h"
#include "string.h"
#include "ctype.h"
#include "stdbool.h"
#include "assert.h"

typedef enum
{
    TK_PUNCT,
    TK_IDENT,
    TK_NUM,
    TK_KEYWORD,
    TK_EOF,
} TokenKind;

typedef struct Token Token;

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
    ND_ADD,       // +
    ND_SUB,       // -
    ND_MUL,       // *
    ND_DIV,       // /
    ND_NEG,       // unary -
    ND_EQ,        // ==
    ND_NE,        // !=
    ND_LT,        // <
    ND_LE,        // <=
    ND_ASSIGN,    // =
    ND_RETURN,    // return
    ND_BLOCK,     // { .. }
    ND_EXPR_STMT, // Expression statement
    ND_VAR,       // Variable
    ND_NUM        // Integer
} NodeKind;

// Local variable
typedef struct Obj Obj;
struct Obj
{
    Obj *next;
    char *name; // Variable name
    int offset; // Offset from RBP
};

typedef struct Node Node;
struct Node
{
    NodeKind kind;
    Node *next;
    Node *lhs;
    Node *rhs;
    Node *body; // use if kind == ND_BLOCK
    int val;    // Used if kind == ND_NUM
    Obj *var;   // Used if kind == ND_VAR
};

typedef struct Function Function;
struct Function
{
    Node *body;
    Obj *locals;
    int stack_size;
};

void error(char *fmt, ...);
void error_tok(Token *tok, char *fmt, ...);

bool equal(Token *tok, char *p);

Token *tokenize(char *p);
Function *parse(Token *tok);
void codegen(Function *prog);
