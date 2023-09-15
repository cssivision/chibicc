#include "chibicc.h"

static Obj *current_fn;

// Variable attributes such as typedef or extern.
typedef struct
{
    bool is_typedef;
} VarAttr;

Node *new_add(Node *lhs, Node *rhs, Token *tok);
Node *expr(Token **rest, Token *tok);
Type *typename(Token **rest, Token *tok);
char *get_ident(Token *tok);
long get_num(Token *tok);
bool is_typename(Token *tok);
Node *unary(Token **rest, Token *tok);
Token *parse_typedef(Token *tok, Type *basety);
Node *compound_stmt(Token **rest, Token *tok);
Node *assign(Token **rest, Token *tok);
Type *declarator(Token **rest, Token *tok, Type *ty);
Type *declspec(Token **rest, Token *tok, VarAttr *attr);

// Scope for local variables, global variables, typedefs
// or enum constants
typedef struct VarScope VarScope;
struct VarScope
{
    VarScope *next;
    char *name;
    Obj *var;
    Type *ty_def;
    Type *enum_ty;
    int enum_val;
};

typedef struct TagScope TagScope;
struct TagScope
{
    TagScope *next;
    char *name;
    Type *ty;
};

typedef struct Scope Scope;
struct Scope
{
    Scope *next;

    // C has two block scopes; one is for variables/typedefs and
    // the other is for struct/union/enum tags.
    VarScope *vars;
    TagScope *tags;
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

static VarScope *push_scope(char *name)
{
    VarScope *vs = calloc(1, sizeof(VarScope));
    vs->name = name;
    vs->next = scope->vars;
    scope->vars = vs;
    return vs;
}

static void push_tag_scope(Token *tok, Type *ty)
{
    TagScope *ts = calloc(1, sizeof(TagScope));
    ts->name = strndup(tok->loc, tok->len);
    ts->ty = ty;
    ts->next = scope->tags;
    scope->tags = ts;
}

Type *find_tag(Token *tag)
{
    for (Scope *sc = scope; sc; sc = sc->next)
    {
        for (TagScope *ts = sc->tags; ts; ts = ts->next)
        {
            if (strncmp(tag->loc, ts->name, tag->len) == 0)
            {
                return ts->ty;
            }
        }
    }
    return NULL;
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

Node *new_num(int64_t val, Token *tok)
{
    Node *node = new_node(ND_NUM, tok);
    node->val = val;
    return node;
}

Node *new_long(int64_t val, Token *tok)
{
    Node *node = new_node(ND_NUM, tok);
    node->val = val;
    node->ty = ty_long;
    return node;
}

Node *new_var_node(Obj *var, Token *tok)
{
    Node *node = new_node(ND_VAR, tok);
    node->var = var;
    return node;
}

// Find a variable by name.
static VarScope *find_var(Token *tok)
{
    for (Scope *sc = scope; sc; sc = sc->next)
    {
        for (VarScope *sc2 = sc->vars; sc2; sc2 = sc2->next)
        {
            if (equal(tok, sc2->name))
            {
                return sc2;
            }
        }
    }
    return NULL;
}

Type *find_typedef(Token *tok)
{
    if (tok->kind == TK_IDENT)
    {
        VarScope *vs = find_var(tok);
        if (vs)
        {
            return vs->ty_def;
        }
    }
    return NULL;
}

Obj *new_var(char *name, Type *ty)
{
    Obj *var = calloc(1, sizeof(Obj));
    var->name = name;
    var->ty = ty;
    push_scope(name)->var = var;
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
    VarScope *sc = find_var(tok);
    if (!sc)
    {
        error_tok(tok, "implicit declaration of a function");
    }
    if (!sc->var || sc->var->ty->kind != TY_FUNC)
    {
        error_tok(tok, "not a function");
    }
    node->funcname = strndup(tok->loc, tok->len);
    tok = tok->next;
    tok = skip(tok, "(");
    Type *ty = sc->var->ty;
    Type *param_ty = ty->params;

    Node head = {};
    Node *cur = &head;
    int i = 0;
    while (!equal(tok, ")"))
    {
        if (i++ > 0)
        {
            tok = skip(tok, ",");
        }
        Node *arg = assign(&tok, tok);
        add_type(arg);
        if (param_ty)
        {
            if (param_ty->kind == TY_STRUCT || param_ty->kind == TY_UNION)
            {
                error_tok(arg->tok, "passing struct or union is not supported yet");
            }
            arg = new_cast(arg, param_ty);
            param_ty = param_ty->next;
        }
        cur = cur->next = arg;
    }
    tok = skip(tok, ")");
    node->args = head.next;
    node->ty = ty->return_ty;
    node->func_ty = ty;
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
//          | sizeof "(" type-name ")"
//          | str
Node *primary(Token **rest, Token *tok)
{
    Token *start = tok;
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

    if (equal(tok, "sizeof") && equal(tok->next, "(") && is_typename(tok->next->next))
    {
        tok = tok->next->next;
        Type *ty = typename(&tok, tok);
        tok = skip(tok, ")");
        *rest = tok;
        return new_num(ty->size, start);
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

        VarScope *vs = find_var(tok);
        if (!vs || (!vs->var && !vs->enum_ty))
        {
            error_tok(tok, "undefined variable");
        }

        Node *node;
        if (vs->var)
        {
            node = new_var_node(vs->var, tok);
        }
        else
        {
            node = new_num(vs->enum_val, tok);
        }
        *rest = tok->next;
        return node;
    }

    error_tok(tok, "expected an expression");
}

Member *get_struct_member(Type *ty, Token *tok)
{
    for (Member *mem = ty->members; mem; mem = mem->next)
    {
        if (mem->name->len == tok->len &&
            !strncmp(mem->name->loc, tok->loc, tok->len))
        {
            return mem;
        }
    }
    error_tok(tok, "no such member");
}

Node *struct_ref(Token *tok, Node *lhs)
{
    if (tok->kind != TK_IDENT)
    {
        error_tok(tok, "expecetd an ident");
    }
    add_type(lhs);
    if (lhs->ty->kind != TY_STRUCT && lhs->ty->kind != TY_UNION)
    {
        error_tok(lhs->tok, "not a struct");
    }
    Node *node = new_unary(ND_MEMBER, lhs, tok);
    node->member = get_struct_member(lhs->ty, tok);
    return node;
}

// postfix = primary ("[" expr "]" | "." ident  | "->" ident )*
static Node *postfix(Token **rest, Token *tok)
{
    Node *node = primary(&tok, tok);

    for (;;)
    {
        if (equal(tok, "["))
        {
            // x[y] is short for *(x+y)
            Token *start = tok;
            Node *idx = expr(&tok, tok->next);
            tok = skip(tok, "]");
            node = new_unary(ND_DEREF, new_add(node, idx, start), start);
            continue;
        }

        if (equal(tok, "."))
        {
            tok = tok->next;
            node = struct_ref(tok, node);
            tok = tok->next;
            continue;
        }
        if (equal(tok, "->"))
        {
            // x->y is short for (*x).y
            node = new_unary(ND_DEREF, node, tok);
            tok = tok->next;
            node = struct_ref(tok, node);
            tok = tok->next;
            continue;
        }
        *rest = tok;
        return node;
    }
}

Node *new_cast(Node *lhs, Type *ty)
{
    add_type(lhs);
    Node *node = new_node(ND_CAST, lhs->tok);
    node->ty = copy_type(ty);
    node->lhs = lhs;
    return node;
}

// cast = "(" type-name ")" cast | unary
Node *cast(Token **rest, Token *tok)
{
    if (equal(tok, "(") && is_typename(tok->next))
    {
        tok = tok->next;
        Type *ty = typename(&tok, tok);
        tok = skip(tok, ")");
        Node *node = new_cast(cast(&tok, tok), ty);
        *rest = tok;
        return node;
    }
    return unary(rest, tok);
}

// unary = ("+" | "-" | "&" | "*") cast
//       | postfix
Node *unary(Token **rest, Token *tok)
{
    if (equal(tok, "+"))
    {
        Node *node = cast(&tok, tok->next);
        *rest = tok;
        return node;
    }

    if (equal(tok, "-"))
    {
        Node *node = new_unary(ND_NEG, cast(&tok, tok->next), tok);
        *rest = tok;
        return node;
    }

    if (equal(tok, "&"))
    {
        Node *node = new_unary(ND_ADDR, cast(&tok, tok->next), tok);
        *rest = tok;
        return node;
    }

    if (equal(tok, "*"))
    {
        Node *node = new_unary(ND_DEREF, cast(&tok, tok->next), tok);
        *rest = tok;
        return node;
    }

    return postfix(rest, tok);
}

// mul = cast ("*" cast | "/" cast)*
Node *mul(Token **rest, Token *tok)
{
    Node *node = cast(&tok, tok);

    for (;;)
    {
        Token *start = tok;
        if (equal(tok, "*"))
        {
            node = new_binary(ND_MUL, node, cast(&tok, tok->next), start);
            continue;
        }

        if (equal(tok, "/"))
        {
            node = new_binary(ND_DIV, node, cast(&tok, tok->next), start);
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
    rhs = new_binary(ND_MUL, rhs, new_long(lhs->ty->base->size, tok), tok);
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
        rhs = new_binary(ND_MUL, rhs, new_long(lhs->ty->base->size, tok), tok);
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
        Node *rhs = assign(&tok, tok->next);
        node = new_binary(ND_ASSIGN, node, rhs, tok);
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

// struct-members = (declspec declarator ("," declarator)* ";")*
void struct_members(Token **rest, Token *tok, Type *ty)
{
    Member head = {};
    Member *cur = &head;
    while (!equal(tok, "}"))
    {
        int i = 0;
        Type *basety = declspec(&tok, tok, NULL);
        while (!equal(tok, ";"))
        {
            if (i++ > 0)
            {
                tok = skip(tok, ",");
            }
            Type *ty = declarator(&tok, tok, basety);
            Member *mem = calloc(1, sizeof(Member));
            mem->ty = ty;
            mem->name = ty->name;
            cur = cur->next = mem;
        }
        tok = skip(tok, ";");
    }
    tok = skip(tok, "}");
    *rest = tok;
    ty->members = head.next;
}

// struct-union-decl = ident? ("{" struct-members )
//                    | ident ("{" struct-members )?
Type *struct_union_decl(Token **rest, Token *tok)
{
    Token *tag = NULL;
    if (tok->kind == TK_IDENT)
    {
        tag = tok;
        tok = tok->next;
    }
    if (tag && !equal(tok, "{"))
    {
        Type *ty = find_tag(tag);
        if (!ty)
        {
            error_tok(tag, "unknow type");
        }
        if (ty->kind != TY_STRUCT && ty->kind != TY_UNION)
        {
            error_tok(tag, "not an tag");
        }
        *rest = tok;
        return ty;
    }

    tok = skip(tok, "{");

    Type *ty = calloc(1, sizeof(Type));
    ty->kind = TY_STRUCT;
    struct_members(&tok, tok, ty);
    ty->align = 1;

    if (tag)
    {
        push_tag_scope(tag, ty);
    }
    *rest = tok;
    return ty;
}

static Type *struct_decl(Token **rest, Token *tok)
{
    Type *ty = struct_union_decl(&tok, tok);
    ty->kind = TY_STRUCT;

    // Assign offsets within the struct to members.
    int offset = 0;
    for (Member *mem = ty->members; mem; mem = mem->next)
    {
        offset = align_to(offset, mem->ty->align);
        mem->offset = offset;
        offset += mem->ty->size;
        if (ty->align < mem->ty->align)
        {
            ty->align = mem->ty->align;
        }
    }
    ty->size = align_to(offset, ty->align);
    *rest = tok;
    return ty;
}

static Type *union_decl(Token **rest, Token *tok)
{
    Type *ty = struct_union_decl(&tok, tok);
    ty->kind = TY_UNION;

    // If union, we don't have to assign offsets because they
    // are already initialized to zero. We need to compute the
    // alignment and the size though.
    for (Member *mem = ty->members; mem; mem = mem->next)
    {
        if (ty->align < mem->ty->align)
        {
            ty->align = mem->ty->align;
        }
        if (ty->size < mem->ty->size)
        {
            ty->size = mem->ty->size;
        }
    }
    ty->size = align_to(ty->size, ty->align);
    *rest = tok;
    return ty;
}

// enum-specifier = ident? "{" enum-list? "}"
//                | ident ("{" enum-list? "}")?
// enum-list      = ident ("=" num)? ("," ident ("=" num)?)*
Type *enum_specifier(Token **rest, Token *tok)
{
    Type *ty = enum_type();
    Token *tag = NULL;
    if (tok->kind == TK_IDENT)
    {
        tag = tok;
        tok = tok->next;
    }

    if (tag && !equal(tok, "{"))
    {
        Type *ty = find_tag(tag);
        if (!ty)
        {
            error_tok(tag, "unknown enum type");
        }
        if (ty->kind != TY_ENUM)
        {
            error_tok(tag, "not an enum tag");
        }
        *rest = tok;
        return ty;
    }

    tok = skip(tok, "{");
    // Read an enum-list.
    int i = 0;
    int val = 0;
    while (!equal(tok, "}"))
    {
        if (i++ > 0)
        {
            tok = skip(tok, ",");
        }
        char *name = get_ident(tok);
        tok = tok->next;

        if (equal(tok, "="))
        {
            val = get_num(tok->next);
            tok = tok->next->next;
        }
        VarScope *vs = push_scope(name);
        vs->enum_ty = ty;
        vs->enum_val = val++;
    }
    tok = tok->next;

    if (tag)
    {
        push_tag_scope(tag, ty);
    }
    *rest = tok;
    return ty;
}

// declspec = ( "void" | "int" | "char" | _Bool | "long" | "typedef"
//              struct-decl | union_decl  | typedef-name )+
//
// The order of typenames in a type-specifier doesn't matter. For
// example, `int long static` means the same as `static long int`.
// That can also be written as `static long` because you can omit
// `int` if `long` or `short` are specified. However, something like
// `char int` is not a valid type specifier. We have to accept only a
// limited combinations of the typenames.
//
// In this function, we count the number of occurrences of each typename
// while keeping the "current" type object that the typenames up
// until that point represent. When we reach a non-typename token,
// we returns the current type object.
Type *declspec(Token **rest, Token *tok, VarAttr *attr)
{
    // We use a single integer as counters for all typenames.
    // For example, bits 0 and 1 represents how many times we saw the
    // keyword "void" so far. With this, we can use a switch statement
    // as you can see below.
    enum
    {
        VOID = 1 << 0,
        BOOL = 1 << 2,
        CHAR = 1 << 4,
        SHORT = 1 << 6,
        INT = 1 << 8,
        LONG = 1 << 10,
        OTHER = 1 << 12,
    };

    Type *ty = ty_int;
    int counter = 0;

    while (is_typename(tok))
    {
        if (equal(tok, "typedef"))
        {
            if (!attr)
            {
                error_tok(tok, "storage class specifier is not allowed in this context");
            }
            attr->is_typedef = true;
            tok = tok->next;
            continue;
        }

        Type *ty2 = find_typedef(tok);
        if (equal(tok, "struct") || equal(tok, "union") || equal(tok, "enum") || ty2)
        {
            if (counter)
            {
                break;
            }

            if (equal(tok, "struct"))
            {
                ty = struct_decl(&tok, tok->next);
            }
            else if (equal(tok, "union"))
            {
                ty = union_decl(&tok, tok->next);
            }
            else if (equal(tok, "enum"))
            {
                ty = enum_specifier(&tok, tok->next);
            }
            else
            {
                ty = ty2;
                tok = tok->next;
            }
            counter += OTHER;
            continue;
        }

        if (equal(tok, "void"))
        {
            counter += VOID;
        }
        else if (equal(tok, "char"))
        {
            counter += CHAR;
        }
        else if (equal(tok, "int"))
        {
            counter += INT;
        }
        else if (equal(tok, "long"))
        {
            counter += LONG;
        }
        else if (equal(tok, "short"))
        {
            counter += SHORT;
        }
        else if (equal(tok, "_Bool"))
        {
            counter += BOOL;
        }
        else
        {
            unreachable();
        }

        switch (counter)
        {
        case VOID:
            ty = ty_void;
            break;
        case BOOL:
            ty = ty_bool;
            break;
        case CHAR:
            ty = ty_char;
            break;
        case SHORT:
        case SHORT + INT:
            ty = ty_short;
            break;
        case INT:
            ty = ty_int;
            break;
        case LONG:
        case LONG + INT:
        case LONG + LONG:
        case LONG + LONG + INT:
            ty = ty_long;
            break;
        default:
            error_tok(tok, "invalid type");
        }
        tok = tok->next;
    }

    *rest = tok;
    return ty;
}

// func-params = param ("," param)*
// param = declspec declarator
Type *func_params(Token **rest, Token *tok, Type *ty)
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
        Type *basety = declspec(&tok, tok, NULL);
        Type *ty = declarator(&tok, tok, basety);
        cur = cur->next = copy_type(ty);
    }
    ty = func_type(ty);
    ty->params = head.next;
    *rest = tok;
    return ty;
}

long get_num(Token *tok)
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
        ty = func_params(&tok, tok->next, ty);
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

// abstract-declarator = "*"* ("(" abstract-declarator ")")? type-suffix
static Type *abstract_declarator(Token **rest, Token *tok, Type *ty)
{
    while (equal(tok, "*"))
    {
        ty = pointer_to(ty);
        tok = tok->next;
    }

    if (equal(tok, "("))
    {
        Token *start = tok;
        Type dummy = {};
        abstract_declarator(&tok, start->next, &dummy);
        tok = skip(tok, ")");
        ty = type_suffix(rest, tok, ty);
        return abstract_declarator(&tok, start->next, ty);
    }

    return type_suffix(rest, tok, ty);
}

Type *typename(Token **rest, Token *tok)
{
    Type *basety = declspec(&tok, tok, NULL);
    Type *ty = abstract_declarator(&tok, tok, basety);
    *rest = tok;
    return ty;
}

// declarator = "*"* ("(" ident ")" | "(" declarator ")" | ident) type-suffix
Type *declarator(Token **rest, Token *tok, Type *ty)
{
    while (consume(&tok, tok, "*"))
    {
        ty = pointer_to(ty);
    }

    if (equal(tok, "("))
    {
        Token *start = tok;
        Type dummy = {};
        declarator(&tok, start->next, &dummy);
        tok = skip(tok, ")");
        ty = type_suffix(rest, tok, ty);
        return declarator(&tok, start->next, ty);
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

char *get_ident(Token *tok)
{
    if (tok->kind != TK_IDENT)
    {
        error_tok(tok, "expected an identifier");
    }
    return strndup(tok->loc, tok->len);
}

// declaration = declspec (declarator ("=" assign)? (",", declarator ("=" assign)?)*)? ";"
Node *declaration(Token **rest, Token *tok, Type *basety)
{
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
        if (ty->kind == TY_VOID)
        {
            error_tok(tok, "variable declared void");
        }
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
        Node *node = new_node(ND_RETURN, tok);
        Node *exp = expr(&tok, tok->next);
        tok = skip(tok, ";");
        add_type(exp);

        node->lhs = new_cast(exp, current_fn->ty->return_ty);
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
    static char *kw[] = {
        "void",
        "char",
        "short",
        "int",
        "long",
        "struct",
        "union",
        "typedef",
        "_Bool",
        "enum",
    };

    for (int i = 0; i < sizeof(kw) / sizeof(*kw); i++)
    {
        if (equal(tok, kw[i]))
        {
            return true;
        }
    }
    return find_typedef(tok);
}

// compound_stmt = (typedef | declaration | stmt)* "}"
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
            VarAttr attr = {};
            Type *basety = declspec(&tok, tok, &attr);
            if (attr.is_typedef)
            {
                tok = parse_typedef(tok, basety);
                continue;
            }
            cur = cur->next = declaration(&tok, tok, basety);
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
    fn->is_definition = !consume(&tok, tok, ";");
    if (!fn->is_definition)
    {
        return tok;
    }

    current_fn = fn;
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

// typedef = (declatator ("," declarator)*)*
Token *parse_typedef(Token *tok, Type *basety)
{
    int i = 0;
    while (!consume(&tok, tok, ";"))
    {
        if (i++ > 0)
        {
            tok = skip(tok, ",");
        }
        Type *ty = declarator(&tok, tok, basety);
        push_scope(get_ident(ty->name))->ty_def = ty;
    }
    return tok;
}

// program = (typedef | function-definition | global-variable)*
Obj *parse(Token *tok)
{
    globals = NULL;
    while (tok->kind != TK_EOF)
    {
        VarAttr attr = {};
        Type *basety = declspec(&tok, tok, &attr);
        if (attr.is_typedef)
        {
            tok = parse_typedef(tok, basety);
            continue;
        }

        if (is_function(tok))
        {
            tok = function(tok, basety);
            continue;
        }
        tok = global_variable(tok, basety);
    }
    return globals;
}