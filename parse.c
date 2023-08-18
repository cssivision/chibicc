#include "chibicc.h"

// All local variable instances created during parsing are
// accumulated to this list.
Obj *locals;

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
    {
        error_tok(tok, "expected '%s'", op);
    }
    return tok->next;
}

Node *new_num(int val)
{
    Node *node = new_node(ND_NUM);
    node->val = val;
    return node;
}

Node *new_var_node(Obj *var)
{
    Node *node = new_node(ND_VAR);
    node->var = var;
    return node;
}

Obj *find_var(Token *tok)
{
    for (Obj *var = locals; var; var = var->next)
    {
        if (strlen(var->name) == tok->len && strncmp(var->name, tok->loc, tok->len) == 0)
        {
            return var;
        }
    }
    return NULL;
}

Obj *new_lvar(char *name)
{
    Obj *var = calloc(1, sizeof(Obj));
    var->name = name;
    var->next = locals;
    locals = var;
    return var;
}

// primary = "(" expr ")" | ident | num
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

    if (tok->kind == TK_IDENT)
    {
        Obj *var = find_var(tok);
        if (!var)
        {
            var = new_lvar(strndup(tok->loc, tok->len));
        }
        *rest = tok->next;
        return new_var_node(var);
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

// assign = equality ("=" assign)?
Node *assign(Token **rest, Token *tok)
{
    Node *node = equality(&tok, tok);
    if (equal(tok, "="))
    {
        node = new_binary(ND_ASSIGN, node, assign(&tok, tok->next));
    }
    *rest = tok;
    return node;
}

// expr = assign
Node *expr(Token **rest, Token *tok)
{
    return assign(rest, tok);
}

// expr-stmt = expr ";"
static Node *expr_stmt(Token **rest, Token *tok)
{
    Node *node = new_unary(ND_EXPR_STMT, expr(&tok, tok));
    *rest = skip(tok, ";");
    return node;
}

// stmt = "return" expr ";"
//      | expr-stmt
//      | "{" stmt* "}"
static Node *stmt(Token **rest, Token *tok)
{
    if (equal(tok, "return"))
    {
        Node *node = new_unary(ND_RETURN, expr(&tok, tok->next));
        tok = skip(tok, ";");
        *rest = tok;
        return node;
    }
    if (equal(tok, "{"))
    {
        Node head = {};
        Node *cur = &head;
        tok = tok->next;
        while (!equal(tok, "}"))
        {
            cur = cur->next = stmt(&tok, tok);
        }
        tok = skip(tok, "}");
        Node *node = new_node(ND_BLOCK);
        node->body = head.next;
        *rest = tok;
        return node;
    }
    return expr_stmt(rest, tok);
}

Function *parse(Token *tok)
{
    Node head = {};
    Node *cur = &head;
    while (tok->kind != TK_EOF)
    {
        cur = cur->next = stmt(&tok, tok);
    }
    Function *prog = calloc(1, sizeof(Function));
    prog->body = head.next;
    prog->locals = locals;
    return prog;
}