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
    TK_NUM,
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
    ND_EXPR_STMT, // Expression statement
    ND_NUM,       // Integer
} NodeKind;

typedef struct Node Node;
struct Node
{
    NodeKind kind;
    Node *next;
    Node *lhs;
    Node *rhs;
    int val;
};

void error(char *fmt, ...);
void error_tok(Token *tok, char *fmt, ...);
Token *tokenize(char *p);
Node *parse(Token *tok);
void codegen(Node *node);
