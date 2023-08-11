#include "chibicc.h"

Node *expr(Token **rest, Token *tok);

bool equal(Token *tok, char *p)
{
    return memcmp(tok->loc, p, tok->len) == 0 && p[tok->len] == '\0';
}

Node *new_node(NodeKind kind)
{
    Node *node = calloc(1, sizeof(Node));
    node->kind = kind;
    return node;
}

Node *new_binary(NodeKind kind, Node *lhs, Node *rhs)
{
    Node *node = new_node(kind);
    node->lhs = lhs;
    node->rhs = rhs;
    return node;
}

Node *new_unary(NodeKind kind, Node *expr)
{
    Node *node = new_node(kind);
    node->lhs = expr;
    return node;
}

Token *skip(Token *tok, char *op)
{
    if (!equal(tok, op))
        error_tok(tok, "expected '%s'", op);
    return tok->next;
}

Node *new_num(int val)
{
    Node *node = new_node(ND_NUM);
    node->val = val;
    return node;
}

// primary = "(" expr ")" | num
Node *primary(Token **rest, Token *tok)
{
    if (equal(tok, "("))
    {
        Node *node = expr(&tok, tok->next);
        *rest = skip(tok, ")");
        return node;
    }

    if (tok->kind == TK_NUM)
    {
        Node *node = new_num(tok->val);
        *rest = tok->next;
        return node;
    }

    error_tok(tok, "expected an expression");
}

// unary = ("+" | "-") unary
//       | primary
Node *unary(Token **rest, Token *tok)
{
    if (equal(tok, "+"))
    {
        Node *node = unary(&tok, tok->next);
        *rest = tok;
        return node;
    }

    if (equal(tok, "-"))
    {
        Node *node = new_unary(ND_NEG, unary(&tok, tok->next));
        *rest = tok;
        return node;
    }

    return primary(rest, tok);
}

// mul = unary ("*" unary | "/" unary)*
Node *mul(Token **rest, Token *tok)
{
    Node *node = unary(&tok, tok);

    for (;;)
    {
        if (equal(tok, "*"))
        {
            node = new_binary(ND_MUL, node, unary(&tok, tok->next));
            continue;
        }

        if (equal(tok, "/"))
        {
            node = new_binary(ND_DIV, node, unary(&tok, tok->next));
            continue;
        }

        *rest = tok;
        return node;
    }
}

// add = mul ("+" mul | "-" mul)*
Node *add(Token **rest, Token *tok)
{
    Node *node = mul(&tok, tok);

    for (;;)
    {
        if (equal(tok, "+"))
        {
            node = new_binary(ND_ADD, node, mul(&tok, tok->next));
            continue;
        }

        if (equal(tok, "-"))
        {
            node = new_binary(ND_SUB, node, mul(&tok, tok->next));
            continue;
        }

        *rest = tok;
        return node;
    }
}

// relational = add ("<" add | "<=" add | ">" add | ">=" add)*
Node *relational(Token **rest, Token *tok)
{
    Node *node = add(&tok, tok);

    for (;;)
    {
        if (equal(tok, "<"))
        {
            node = new_binary(ND_LT, node, add(&tok, tok->next));
            continue;
        }

        if (equal(tok, "<="))
        {
            node = new_binary(ND_LE, node, add(&tok, tok->next));
            continue;
        }

        if (equal(tok, ">"))
        {
            node = new_binary(ND_LT, add(&tok, tok->next), node);
            continue;
        }

        if (equal(tok, ">="))
        {
            node = new_binary(ND_LE, add(&tok, tok->next), node);
            continue;
        }

        *rest = tok;
        return node;
    }
}

// equality = relational ("==" relational | "!=" relational)*
Node *equality(Token **rest, Token *tok)
{
    Node *node = relational(&tok, tok);

    for (;;)
    {
        if (equal(tok, "=="))
        {
            node = new_binary(ND_EQ, node, relational(&tok, tok->next));
            continue;
        }

        if (equal(tok, "!="))
        {
            node = new_binary(ND_NE, node, relational(&tok, tok->next));
            continue;
        }

        *rest = tok;
        return node;
    }
}

// expr = equality
Node *expr(Token **rest, Token *tok)
{
    return equality(rest, tok);
}

Node *parse(Token *tok)
{
    Node *node = expr(&tok, tok);
    if (tok->kind != TK_EOF)
        error_tok(tok, "extra token");
    return node;
}