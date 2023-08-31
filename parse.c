#include "chibicc.h"

Node *new_add(Node *lhs, Node *rhs, Token *tok);
Node *expr(Token **rest, Token *tok);
Node *unary(Token **rest, Token *tok);
Node *compound_stmt(Token **rest, Token *tok);
Node *assign(Token **rest, Token *tok);
Type *declarator(Token **rest, Token *tok, Type *ty);
Type *declspec(Token **rest, Token *tok);

typedef struct VarScope VarScope;
struct VarScope
{
    VarScope *next;
    char *name;
    Obj *var;
};

typedef struct Scope Scope;
struct Scope
{
    Scope *next;
    VarScope *vars;
};

// All local variable instances created during parsing are
// accumulated to this list.
Obj *locals;
Obj *globals;
static Scope *scope = &(Scope){};

static void enter_scope()
{
    Scope *sc = calloc(1, sizeof(Scope));
    sc->next = scope;
    scope = sc;
}

static void leave_scope(void)
{
    scope = scope->next;
}

static void push_scope(char *name, Obj *var)
{
    VarScope *vs = calloc(1, sizeof(VarScope));
    vs->name = name;
    vs->var = var;
    vs->next = scope->vars;
    scope->vars = vs;
}

bool equal(Token *tok, char *p)
{
    return memcmp(tok->loc, p, tok->len) == 0 && p[tok->len] == '\0';
}

Node *new_node(NodeKind kind, Token *tok)
{
    Node *node = calloc(1, sizeof(Node));
    node->kind = kind;
    node->tok = tok;
    return node;
}

Node *new_binary(NodeKind kind, Node *lhs, Node *rhs, Token *tok)
{
    Node *node = new_node(kind, tok);
    node->lhs = lhs;
    node->rhs = rhs;
    return node;
}

Node *new_unary(NodeKind kind, Node *expr, Token *tok)
{
    Node *node = new_node(kind, tok);
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

Node *new_num(int val, Token *tok)
{
    Node *node = new_node(ND_NUM, tok);
    node->val = val;
    return node;
}

Node *new_var_node(Obj *var, Token *tok)
{
    Node *node = new_node(ND_VAR, tok);
    node->var = var;
    return node;
}

// Find a variable by name.
static Obj *find_var(Token *tok)
{
    for (Scope *sc = scope; sc; sc = sc->next)
    {
        for (VarScope *sc2 = sc->vars; sc2; sc2 = sc2->next)
        {
            if (equal(tok, sc2->name))
            {
                return sc2->var;
            }
        }
    }
    return NULL;
}

Obj *new_var(char *name, Type *ty)
{
    Obj *var = calloc(1, sizeof(Obj));
    var->name = name;
    var->ty = ty;
    push_scope(name, var);
    return var;
}

Obj *new_lvar(char *name, Type *ty)
{
    Obj *var = new_var(name, ty);
    var->is_local = true;
    var->next = locals;
    locals = var;
    return var;
}

Obj *new_gvar(char *name, Type *ty)
{
    Obj *var = new_var(name, ty);
    var->next = globals;
    globals = var;
    return var;
}

// funcall = ident "(" (assign ("," assign)*)? ")"
Node *funccall(Token **rest, Token *tok)
{
    Node *node = new_node(ND_FUNCCALL, tok);
    node->funcname = strndup(tok->loc, tok->len);
    tok = tok->next;
    tok = skip(tok, "(");

    Node head = {};
    Node *cur = &head;

    int i = 0;
    while (!equal(tok, ")"))
    {
        if (i++ > 0)
        {
            tok = skip(tok, ",");
        }
        cur = cur->next = assign(&tok, tok);
    }
    tok = skip(tok, ")");
    node->args = head.next;
    *rest = tok;
    return node;
}

char *new_unique_name()
{
    static int id = 0;
    return format(".L..%d", id++);
}

Obj *new_anon_gvar(Type *ty)
{
    return new_gvar(new_unique_name(), ty);
}

Obj *new_string_literal(char *str, Type *ty)
{
    Obj *var = new_anon_gvar(ty);
    var->init_data = str;
    return var;
}

// primary = "(" expr ")"
//          | ("{" stmt+ "}")
//          | ident func-args?
//          | num
//          | sizeof unary
//          | str
Node *primary(Token **rest, Token *tok)
{
    if (equal(tok, "(") && equal(tok->next, "{"))
    {
        // This is a GNU statement expresssion.
        tok = tok->next->next;
        Node *node = new_node(ND_STMT_EXPR, tok);
        node->body = compound_stmt(&tok, tok)->body;
        tok = skip(tok, ")");
        *rest = tok;
        return node;
    }

    if (equal(tok, "("))
    {
        Node *node = expr(&tok, tok->next);
        *rest = skip(tok, ")");
        return node;
    }

    if (equal(tok, "sizeof"))
    {
        Node *node = unary(&tok, tok->next);
        add_type(node);
        *rest = tok;
        return new_num(node->ty->size, tok);
    }

    if (tok->kind == TK_STR)
    {
        Obj *var = new_string_literal(tok->str, tok->ty);
        *rest = tok->next;
        return new_var_node(var, tok);
    }

    if (tok->kind == TK_NUM)
    {
        Node *node = new_num(tok->val, tok);
        *rest = tok->next;
        return node;
    }

    if (tok->kind == TK_IDENT)
    {
        if (equal(tok->next, "("))
        {
            return funccall(rest, tok);
        }

        Obj *var = find_var(tok);
        if (!var)
        {
            error_tok(tok, "undefined variable");
        }
        *rest = tok->next;
        return new_var_node(var, tok);
    }

    error_tok(tok, "expected an expression");
}

// postfix = primary ("[" expr "]")*
static Node *postfix(Token **rest, Token *tok)
{
    Node *node = primary(&tok, tok);

    while (equal(tok, "["))
    {
        // x[y] is short for *(x+y)
        Token *start = tok;
        Node *idx = expr(&tok, tok->next);
        tok = skip(tok, "]");
        node = new_unary(ND_DEREF, new_add(node, idx, start), start);
    }
    *rest = tok;
    return node;
}

// unary = ("+" | "-" | "&" | "*") unary
//       | postfix
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
        Node *node = new_unary(ND_NEG, unary(&tok, tok->next), tok);
        *rest = tok;
        return node;
    }

    if (equal(tok, "&"))
    {
        Node *node = new_unary(ND_ADDR, unary(&tok, tok->next), tok);
        *rest = tok;
        return node;
    }

    if (equal(tok, "*"))
    {
        Node *node = new_unary(ND_DEREF, unary(&tok, tok->next), tok);
        *rest = tok;
        return node;
    }

    return postfix(rest, tok);
}

// mul = unary ("*" unary | "/" unary)*
Node *mul(Token **rest, Token *tok)
{
    Node *node = unary(&tok, tok);

    for (;;)
    {
        Token *start = tok;
        if (equal(tok, "*"))
        {
            node = new_binary(ND_MUL, node, unary(&tok, tok->next), start);
            continue;
        }

        if (equal(tok, "/"))
        {
            node = new_binary(ND_DIV, node, unary(&tok, tok->next), start);
            continue;
        }

        *rest = tok;
        return node;
    }
}

// In C, `+` operator is overloaded to perform the pointer arithmetic.
// If p is a pointer, p+n adds not n but sizeof(*p)*n to the value of p,
// so that p+n points to the location n elements (not bytes) ahead of p.
// In other words, we need to scale an integer value before adding to a
// pointer value. This function takes care of the scaling.
Node *new_add(Node *lhs, Node *rhs, Token *tok)
{
    add_type(lhs);
    add_type(rhs);

    // num + num
    if (is_integer(lhs->ty) && is_integer(rhs->ty))
    {
        return new_binary(ND_ADD, lhs, rhs, tok);
    }

    // ptr + ptr
    if (lhs->ty->base && rhs->ty->base)
    {
        error_tok(tok, "invalid operands");
    }

    if (!lhs->ty->base && rhs->ty->base)
    {
        Node *tmp = lhs;
        lhs = rhs;
        rhs = tmp;
    }

    // ptr + num
    rhs = new_binary(ND_MUL, rhs, new_num(lhs->ty->base->size, tok), tok);
    return new_binary(ND_ADD, lhs, rhs, tok);
}

// Like `+`, `-` is overloaded for the pointer type.
static Node *new_sub(Node *lhs, Node *rhs, Token *tok)
{
    add_type(lhs);
    add_type(rhs);

    // num - num
    if (is_integer(lhs->ty) && is_integer(rhs->ty))
    {
        return new_binary(ND_SUB, lhs, rhs, tok);
    }

    // ptr - num
    if (lhs->ty->base && is_integer(rhs->ty))
    {
        rhs = new_binary(ND_MUL, rhs, new_num(lhs->ty->base->size, tok), tok);
        add_type(rhs);
        Node *node = new_binary(ND_SUB, lhs, rhs, tok);
        node->ty = lhs->ty;
        return node;
    }

    // ptr - ptr, which returns how many elements are between the two.
    if (lhs->ty->base && rhs->ty->base)
    {
        Node *node = new_binary(ND_SUB, lhs, rhs, tok);
        node->ty = ty_int;
        return new_binary(ND_DIV, node, new_num(lhs->ty->base->size, tok), tok);
    }

    error_tok(tok, "invalid operands");
}

// add = mul ("+" mul | "-" mul)*
Node *add(Token **rest, Token *tok)
{
    Node *node = mul(&tok, tok);

    for (;;)
    {
        Token *start = tok;
        if (equal(tok, "+"))
        {
            node = new_add(node, mul(&tok, tok->next), start);
            continue;
        }

        if (equal(tok, "-"))
        {
            node = new_sub(node, mul(&tok, tok->next), start);
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
        Token *start = tok;
        if (equal(tok, "<"))
        {
            node = new_binary(ND_LT, node, add(&tok, tok->next), tok);
            continue;
        }

        if (equal(tok, "<="))
        {
            node = new_binary(ND_LE, node, add(&tok, tok->next), tok);
            continue;
        }

        if (equal(tok, ">"))
        {
            node = new_binary(ND_LT, add(&tok, tok->next), node, tok);
            continue;
        }

        if (equal(tok, ">="))
        {
            node = new_binary(ND_LE, add(&tok, tok->next), node, tok);
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
        Token *start = tok;
        if (equal(tok, "=="))
        {
            node = new_binary(ND_EQ, node, relational(&tok, tok->next), start);
            continue;
        }

        if (equal(tok, "!="))
        {
            node = new_binary(ND_NE, node, relational(&tok, tok->next), start);
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
        node = new_binary(ND_ASSIGN, node, assign(&tok, tok->next), tok);
    }
    *rest = tok;
    return node;
}

// expr = assign ("," expr)?
Node *expr(Token **rest, Token *tok)
{
    Node *node = assign(&tok, tok);
    if (equal(tok, ","))
    {
        node = new_binary(ND_COMMA, node, expr(&tok, tok->next), tok);
        *rest = tok;
        return node;
    }
    *rest = tok;
    return node;
}

// expr-stmt = expr? ";"
static Node *expr_stmt(Token **rest, Token *tok)
{
    if (equal(tok, ";"))
    {
        tok = tok->next;
        *rest = tok;
        return new_node(ND_BLOCK, tok);
    }
    Node *node = new_unary(ND_EXPR_STMT, expr(&tok, tok), tok);
    *rest = skip(tok, ";");
    return node;
}

// declspec = "int" | "char"
Type *declspec(Token **rest, Token *tok)
{
    if (equal(tok, "char"))
    {
        tok = skip(tok, "char");
        *rest = tok;
        return ty_char;
    }
    tok = skip(tok, "int");
    *rest = tok;
    return ty_int;
}

// func-params = param ("," param)*
// param = declspec declarator
Type *func_params(Token **rest, Token *tok)
{
    Type head = {};
    Type *cur = &head;
    int i = 0;
    while (!equal(tok, ")"))
    {
        if (i++ > 0)
        {
            tok = skip(tok, ",");
        }
        Type *basety = declspec(&tok, tok);
        Type *ty = declarator(&tok, tok, basety);
        cur = cur->next = copy_type(ty);
    }
    Type *ty = func_type(ty);
    ty->params = head.next;
    *rest = tok;
    return ty;
}

int get_num(Token *tok)
{
    if (tok->kind != TK_NUM)
    {
        error_tok(tok, "expected a number");
    }
    return tok->val;
}

// type-suffix = ("(" func-params? ")")?
//               | "[" num "]" type-suffix
Type *type_suffix(Token **rest, Token *tok, Type *ty)
{
    if (equal(tok, "("))
    {
        Type *ty = func_params(&tok, tok->next);
        tok = skip(tok, ")");
        *rest = tok;
        return ty;
    }
    if (equal(tok, "["))
    {
        tok = tok->next;
        int len = get_num(tok);
        tok = skip(tok->next, "]");
        ty = type_suffix(&tok, tok, ty);
        *rest = tok;
        return array_of(ty, len);
    }
    *rest = tok;
    return ty;
}

// declarator = "*"* ident type-suffix
Type *declarator(Token **rest, Token *tok, Type *ty)
{
    while (consume(&tok, tok, "*"))
    {
        ty = pointer_to(ty);
    }

    if (tok->kind != TK_IDENT)
    {
        error_tok(tok, "expected a variable name");
    }
    Token *start = tok;
    ty = type_suffix(&tok, tok->next, ty);
    ty->name = start;
    *rest = tok;
    return ty;
}

static char *get_ident(Token *tok)
{
    if (tok->kind != TK_IDENT)
    {
        error_tok(tok, "expected an identifier");
    }
    return strndup(tok->loc, tok->len);
}

// declaration = declspec (declarator ("=" assign)? (",", declarator ("=" assign)?)*)? ";"
Node *declaration(Token **rest, Token *tok)
{
    Type *basety = declspec(&tok, tok);

    Node head = {};
    Node *cur = &head;

    int i = 0;
    while (!equal(tok, ";"))
    {
        if (i++ > 0)
        {
            tok = skip(tok, ",");
        }

        Type *ty = declarator(&tok, tok, basety);
        Obj *var = new_lvar(get_ident(ty->name), ty);

        if (!equal(tok, "="))
        {
            continue;
        }

        Node *lhs = new_var_node(var, ty->name);
        Node *rhs = assign(&tok, tok->next);
        Node *node = new_binary(ND_ASSIGN, lhs, rhs, tok);
        cur = cur->next = new_unary(ND_EXPR_STMT, node, tok);
    }
    Node *node = new_node(ND_BLOCK, tok);
    node->body = head.next;
    *rest = tok->next;
    return node;
}

// stmt = "return" expr ";"
//      | expr-stmt
//      | "{" compound-stmt
//      | "if" "(" expr ")" stmt ("else" stmt)?
//      | "for" "(" expr-stmt expr? ";" expr? ")" stmt
//      | "while" "(" expr ")" stmt
static Node *stmt(Token **rest, Token *tok)
{
    if (equal(tok, "while"))
    {
        tok = skip(tok->next, "(");
        Node *node = new_node(ND_FOR, tok);
        node->cond = expr(&tok, tok);
        tok = skip(tok, ")");
        node->then = stmt(&tok, tok);
        *rest = tok;
        return node;
    }

    if (equal(tok, "for"))
    {
        Node *node = new_node(ND_FOR, tok);
        tok = skip(tok->next, "(");
        node->init = expr_stmt(&tok, tok);
        if (!equal(tok, ";"))
        {
            node->cond = expr(&tok, tok);
        }
        tok = skip(tok, ";");
        if (!equal(tok, ")"))
        {
            node->inc = expr(&tok, tok);
        }
        tok = skip(tok, ")");
        node->then = stmt(&tok, tok);
        *rest = tok;
        return node;
    }

    if (equal(tok, "if"))
    {
        Node *node = new_node(ND_IF, tok);
        tok = skip(tok->next, "(");
        node->cond = expr(&tok, tok);
        tok = skip(tok, ")");
        node->then = stmt(&tok, tok);
        if (equal(tok, "else"))
        {
            node->els = stmt(&tok, tok->next);
        }
        *rest = tok;
        return node;
    }

    if (equal(tok, "return"))
    {
        Token *start = tok;
        Node *node = new_unary(ND_RETURN, expr(&tok, tok->next), start);
        tok = skip(tok, ";");
        *rest = tok;
        return node;
    }

    if (equal(tok, "{"))
    {
        Node *node = compound_stmt(&tok, tok->next);
        *rest = tok;
        return node;
    }
    return expr_stmt(rest, tok);
}

bool is_typename(Token *tok)
{
    return equal(tok, "int") || equal(tok, "char");
}

// compound_stmt = (declaration | stmt)* "}"
Node *compound_stmt(Token **rest, Token *tok)
{
    Node *node = new_node(ND_BLOCK, tok);
    Node head = {};
    Node *cur = &head;
    enter_scope();
    while (!equal(tok, "}"))
    {
        if (is_typename(tok))
        {
            cur = cur->next = declaration(&tok, tok);
        }
        else
        {
            cur = cur->next = stmt(&tok, tok);
        }
        add_type(cur);
    }
    tok = skip(tok, "}");
    leave_scope();
    node->body = head.next;
    *rest = tok;
    return node;
}

void create_param_lvars(Type *param)
{
    if (param)
    {
        create_param_lvars(param->next);
        new_lvar(get_ident(param->name), param);
    }
}

// function = declspec declarator "{" compound_stmt
Token *function(Token *tok, Type *basety)
{
    Type *ty = declarator(&tok, tok, basety);

    Obj *fn = new_gvar(get_ident(ty->name), ty);
    fn->is_function = true;

    locals = NULL;
    enter_scope();
    create_param_lvars(ty->params);
    fn->params = locals;

    tok = skip(tok, "{");
    fn->body = compound_stmt(&tok, tok);
    fn->locals = locals;
    leave_scope();
    return tok;
}

bool is_function(Token *tok)
{
    if (equal(tok, ";"))
    {
        return false;
    }

    Type dummy = {};
    Type *ty = declarator(&tok, tok, &dummy);
    return ty->kind == TY_FUNC;
}

Token *global_variable(Token *tok, Type *basety)
{
    int i = 0;
    while (!equal(tok, ";"))
    {
        if (i++ > 0)
        {
            tok = skip(tok, ",");
        }
        Type *ty = declarator(&tok, tok, basety);
        new_gvar(get_ident(ty->name), ty);
    }
    tok = skip(tok, ";");
    return tok;
}

// program = (function-definition | global-variable)*
Obj *parse(Token *tok)
{
    globals = NULL;
    while (tok->kind != TK_EOF)
    {
        Type *basety = declspec(&tok, tok);
        if (is_function(tok))
        {
            tok = function(tok, basety);
            continue;
        }
        tok = global_variable(tok, basety);
    }
    return globals;
}