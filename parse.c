#include "chibicc.h"

static Obj *current_fn;
// Lists of all goto statements and labels in the curent function.
static Node *gotos;
static Node *labels;

// "break" and "continue" labels
static char *brk_label;
static char *cont_label;

// Points to a node representing a switch if we are parsing
// a switch statement. Otherwise, NULL.
static Node *current_switch;

// Variable attributes such as typedef or extern.
typedef struct
{
    bool is_typedef;
    bool is_static;
    bool is_extern;
    bool is_inline;
    int align;
} VarAttr;

// This struct represents a variable initializer. Since initializers
// can be nested (e.g. `int x[2][2] = {{1, 2}, {3, 4}}`), this struct
// is a tree data structure.
typedef struct Initializer Initializer;
struct Initializer
{
    Initializer *next;
    Type *ty;
    bool is_flexible;
    Obj *var;

    int idx;

    // If it's not an aggregate type and has an initializer,
    // `expr` has an initialization expression.
    Node *expr;

    // If it's an initializer for an aggregate type (e.g. array or struct),
    // `children` has initializers for its children.
    Initializer **children;

    // Only one member can be initialized for a union.
    // `mem` is used to clarify which member is initialized.
    Member *mem;
};

static Node *new_add(Node *lhs, Node *rhs, Token *tok);
static Node *new_sub(Node *lhs, Node *rhs, Token *tok);
static Node *new_node(NodeKind kind, Token *tok);
static Node *expr(Token **rest, Token *tok);
static Type *type_suffix(Token **rest, Token *tok, Type *ty);
static Type *typename(Token **rest, Token *tok);
static char *get_ident(Token *tok);
int64_t const_expr(Token **rest, Token *tok);
static Node *conditional(Token **rest, Token *tok);
static void designation(Token **rest, Token *tok, Initializer *init);
static void gvar_initializer(Token **rest, Token *tok, Obj *var);
static Node *lvar_initializer(Token **rest, Token *tok, Obj *var);
void initializer2(Token **rest, Token *tok, Initializer *init);
static void struct_initializer2(Token **rest, Token *tok, Initializer *init, Member *mem);
static Type *pointers(Token **rest, Token *tok, Type *ty);
static int64_t eval2(Node *node, char **label);
static int64_t eval_rval(Node *node, char **label);
static Node *funccall(Token **rest, Token *tok, Node *fn);
static bool is_typename(Token *tok);
static bool is_function(Token *tok);
static Token *function(Token *tok, Type *basety, VarAttr *attr);
static Token *global_variable(Token *tok, Type *basety, VarAttr *attr);
static Node *unary(Token **rest, Token *tok);
static Token *parse_typedef(Token *tok, Type *basety);
static Node *compound_stmt(Token **rest, Token *tok);
static Node *assign(Token **rest, Token *tok);
static Type *declarator(Token **rest, Token *tok, Type *ty);
static Type *declspec(Token **rest, Token *tok, VarAttr *attr);

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
static Obj *locals;
static Obj *globals;
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
            if (equal(tag, ts->name))
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

static Node *new_node(NodeKind kind, Token *tok)
{
    Node *node = calloc(1, sizeof(Node));
    node->kind = kind;
    node->tok = tok;
    return node;
}

static Node *new_binary(NodeKind kind, Node *lhs, Node *rhs, Token *tok)
{
    Node *node = new_node(kind, tok);
    node->lhs = lhs;
    node->rhs = rhs;
    return node;
}

static Node *new_unary(NodeKind kind, Node *expr, Token *tok)
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

static Node *new_num(int64_t val, Token *tok)
{
    Node *node = new_node(ND_NUM, tok);
    node->val = val;
    return node;
}

static Node *new_long(int64_t val, Token *tok)
{
    Node *node = new_node(ND_NUM, tok);
    node->val = val;
    node->ty = ty_long;
    return node;
}

static Node *new_ulong(int64_t val, Token *tok)
{
    Node *node = new_node(ND_NUM, tok);
    node->val = val;
    node->ty = ty_ulong;
    return node;
}

static Node *new_var_node(Obj *var, Token *tok)
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

static Type *find_typedef(Token *tok)
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

static Obj *new_var(char *name, Type *ty)
{
    Obj *var = calloc(1, sizeof(Obj));
    var->name = name;
    var->ty = ty;
    var->align = ty->align;
    push_scope(name)->var = var;
    return var;
}

static Obj *new_lvar(char *name, Type *ty)
{
    Obj *var = new_var(name, ty);
    var->is_local = true;
    var->next = locals;
    locals = var;
    return var;
}

static Obj *new_gvar(char *name, Type *ty)
{
    Obj *var = new_var(name, ty);
    var->next = globals;
    var->is_definition = true;
    var->is_static = true;
    globals = var;
    return var;
}

// funcall = "(" (assign ("," assign)*)? ")"
static Node *funccall(Token **rest, Token *tok, Node *fn)
{
    add_type(fn);

    if (fn->ty->kind != TY_FUNC &&
        (fn->ty->kind != TY_PTR || fn->ty->base->kind != TY_FUNC))
    {
        error_tok(fn->tok, "not a function");
    }

    Node *node = new_unary(ND_FUNCCALL, fn, tok);
    Type *ty = (fn->ty->kind == TY_FUNC) ? fn->ty : fn->ty->base;
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
        if (!param_ty && !ty->is_variadic)
        {
            error_tok(tok, "too many arguments");
        }

        Node *arg = assign(&tok, tok);
        add_type(arg);
        if (param_ty)
        {
            if (param_ty->kind != TY_STRUCT && param_ty->kind != TY_UNION)
            {
                arg = new_cast(arg, param_ty);
            }
            param_ty = param_ty->next;
        }
        else if (arg->ty->kind == TY_FLOAT)
        {
            // If parameter type is omitted (e.g. in "..."), float
            // arguments are promoted to double.
            arg = new_cast(arg, ty_double);
        }
        cur = cur->next = arg;
    }
    if (param_ty)
    {
        error_tok(tok, "too few arguments");
    }

    tok = skip(tok, ")");
    node->args = head.next;
    node->ty = ty->return_ty;
    *rest = tok;

    // If a function returns a struct, it is caller's responsibility
    // to allocate a space for the return value.
    if (node->ty->kind == TY_STRUCT || node->ty->kind == TY_UNION)
    {
        node->ret_buffer = new_lvar("", node->ty);
    }
    return node;
}

static char *new_unique_name()
{
    static int id = 0;
    return format(".L..%d", id++);
}

static Obj *new_anon_gvar(Type *ty)
{
    return new_gvar(new_unique_name(), ty);
}

static Obj *new_string_literal(char *str, Type *ty)
{
    Obj *var = new_anon_gvar(ty);
    var->init_data = str;
    return var;
}

// generic-selection = "(" assign "," generic-assoc ("," generic-assoc)* ")"
//
// generic-assoc = type-name ":" assign
//               | "default" ":" assign
static Node *generic_selection(Token **rest, Token *tok)
{
    Token *start = tok;
    tok = skip(tok, "(");

    Node *ctrl = assign(&tok, tok);
    add_type(ctrl);

    Type *t1 = ctrl->ty;
    if (t1->kind == TY_FUNC)
    {
        t1 = pointer_to(t1);
    }
    else if (t1->kind == TY_ARRAY)
    {
        t1 = pointer_to(t1->base);
    }

    Node *ret = NULL;
    while (!consume(rest, tok, ")"))
    {
        tok = skip(tok, ",");
        if (equal(tok, "default"))
        {
            tok = skip(tok->next, ":");
            Node *node = assign(&tok, tok);
            if (!ret)
            {
                ret = node;
            }
            continue;
        }

        Type *t2 = typename(&tok, tok);
        tok = skip(tok, ":");
        Node *node = assign(&tok, tok);
        if (is_compatible(t1, t2))
        {
            ret = node;
        }
    }

    if (!ret)
    {
        error_tok(start, "controlling expression type not compatible with"
                         " any generic association type");
    }
    return ret;
}

// primary = "(" expr ")"
//          | ("{" stmt+ "}")
//          | ident
//          | num
//          | sizeof unary
//          | "_Generic" generic-selection
//          | "__builtin_types_compatible_p" "(" type-name, type-name, ")"
//          | "_Alignof" "(" type-name ")"
//          | "_Alignof" unary
//          | sizeof "(" type-name ")"
//          | str
static Node *primary(Token **rest, Token *tok)
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
        return new_ulong(ty->size, start);
    }

    if (equal(tok, "sizeof"))
    {
        Node *node = unary(&tok, tok->next);
        add_type(node);
        *rest = tok;
        return new_ulong(node->ty->size, tok);
    }

    if (equal(tok, "_Alignof") && equal(tok->next, "(") && is_typename(tok->next->next))
    {
        tok = skip(tok->next, "(");
        Type *ty = typename(&tok, tok);
        *rest = skip(tok, ")");
        return new_ulong(ty->align, tok);
    }

    if (equal(tok, "_Alignof"))
    {
        Node *node = unary(&tok, tok->next);
        add_type(node);
        *rest = tok;
        return new_ulong(node->ty->align, tok);
    }

    if (tok->kind == TK_STR)
    {
        Obj *var = new_string_literal(tok->str, tok->ty);
        *rest = tok->next;
        return new_var_node(var, tok);
    }

    if (tok->kind == TK_NUM)
    {

        Node *node;
        if (is_flonum(tok->ty))
        {
            node = new_node(ND_NUM, tok);
            node->fval = tok->fval;
        }
        else
        {
            node = new_num(tok->val, tok);
        }
        node->ty = tok->ty;
        *rest = tok->next;
        return node;
    }

    if (equal(tok, "_Generic"))
    {
        return generic_selection(rest, tok->next);
    }

    if (equal(tok, "__builtin_types_compatible_p"))
    {
        tok = skip(tok->next, "(");
        Type *t1 = typename(&tok, tok);
        tok = skip(tok, ",");
        Type *t2 = typename(&tok, tok);
        *rest = skip(tok, ")");
        return new_num(is_compatible(t1, t2), start);
    }

    if (equal(tok, "__builtin_reg_class"))
    {
        tok = skip(tok->next, "(");
        Type *ty = typename(&tok, tok);
        *rest = skip(tok, ")");

        if (is_integer(ty) || ty->kind == TY_PTR)
        {
            return new_num(0, start);
        }
        if (is_flonum(ty))
        {
            return new_num(1, start);
        }
        return new_num(2, start);
    }

    if (tok->kind == TK_IDENT)
    {
        VarScope *vs = find_var(tok);
        *rest = tok->next;
        if (vs)
        {
            if (vs->var)
            {
                return new_var_node(vs->var, tok);
            }
            else
            {
                return new_num(vs->enum_val, tok);
            }
        }
        if (equal(tok->next, "("))
        {
            error_tok(tok, "implicit declaration of a function");
        }
        error_tok(tok, "undefined variable");
    }

    error_tok(tok, "expected an expression");
}

static Member *get_struct_member(Type *ty, Token *tok)
{
    for (Member *mem = ty->members; mem; mem = mem->next)
    {
        // Anonymous struct member
        if ((mem->ty->kind == TY_STRUCT || mem->ty->kind == TY_UNION) &&
            !mem->name)
        {
            if (get_struct_member(mem->ty, tok))
            {
                return mem;
            }
            continue;
        }

        // Regular struct member
        if (mem->name->len == tok->len &&
            !strncmp(mem->name->loc, tok->loc, tok->len))
        {
            return mem;
        }
    }
    return NULL;
}

static Node *struct_ref(Token *tok, Node *lhs)
{
    add_type(lhs);
    if (lhs->ty->kind != TY_STRUCT && lhs->ty->kind != TY_UNION)
    {
        error_tok(lhs->tok, "not a struct nor a union");
    }

    Type *ty = lhs->ty;
    for (;;)
    {
        Member *mem = get_struct_member(ty, tok);
        if (!mem)
        {
            error_tok(tok, "no such member");
        }
        lhs = new_unary(ND_MEMBER, lhs, tok);
        lhs->member = mem;
        if (mem->name)
        {
            break;
        }
        ty = mem->ty;
    }
    return lhs;
}

// Convert op= operators to expressions containing an assignment.
//
// In general, `A op= C` is converted to ``tmp = &A, *tmp = *tmp op B`.
// However, if a given expression is of form `A.x op= C`, the input is
// converted to `tmp = &A, (*tmp).x = (*tmp).x op C` to handle assignments
// to bitfields.
static Node *to_assign(Node *binary)
{
    add_type(binary->lhs);
    add_type(binary->rhs);
    Token *tok = binary->tok;

    // Convert `A.x op= C` to `tmp = &A, (*tmp).x = (*tmp).x op C`.
    if (binary->lhs->kind == ND_MEMBER)
    {
        Obj *var = new_lvar("", pointer_to(binary->lhs->lhs->ty));

        Node *expr1 = new_binary(ND_ASSIGN, new_var_node(var, tok),
                                 new_unary(ND_ADDR, binary->lhs->lhs, tok), tok);

        Node *expr2 = new_unary(ND_MEMBER,
                                new_unary(ND_DEREF, new_var_node(var, tok), tok),
                                tok);
        expr2->member = binary->lhs->member;

        Node *expr3 = new_unary(ND_MEMBER,
                                new_unary(ND_DEREF, new_var_node(var, tok), tok),
                                tok);
        expr3->member = binary->lhs->member;

        Node *expr4 = new_binary(ND_ASSIGN, expr2,
                                 new_binary(binary->kind, expr3, binary->rhs, tok),
                                 tok);

        return new_binary(ND_COMMA, expr1, expr4, tok);
    }

    // Convert `A op= C` to ``tmp = &A, *tmp = *tmp op B`.

    Obj *var = new_lvar("", pointer_to(binary->lhs->ty));
    Node *expr1 = new_binary(ND_ASSIGN, new_var_node(var, tok),
                             new_unary(ND_ADDR, binary->lhs, tok), tok);
    Node *expr2 =
        new_binary(ND_ASSIGN,
                   new_unary(ND_DEREF, new_var_node(var, tok), tok),
                   new_binary(binary->kind,
                              new_unary(ND_DEREF, new_var_node(var, tok), tok),
                              binary->rhs,
                              tok),
                   tok);
    return new_binary(ND_COMMA, expr1, expr2, tok);
}

static Node *new_inc_dec(Node *node, Token *tok, int addend)
{
    add_type(node);
    return new_cast(new_add(to_assign(new_add(node, new_num(addend, tok), tok)),
                            new_num(-addend, tok), tok),
                    node->ty);
}

// postfix = "(" type-name ")" "{" initializer-list "}"
//         | primary "(" func-args ")" postfix-tail*
//         | primary postfix-tail*
// postfix-tail = "[" expr "]"
//              | "(" func-args ")"
//              | "." ident
//              | "->" ident
//              | "++"
//              | "--"
static Node *postfix(Token **rest, Token *tok)
{
    if (equal(tok, "(") && is_typename(tok->next))
    {
        // Compound literal
        Token *start = tok;
        Type *ty = typename(&tok, tok->next);
        tok = skip(tok, ")");

        if (scope->next == NULL)
        {
            Obj *var = new_anon_gvar(ty);
            gvar_initializer(rest, tok, var);
            return new_var_node(var, start);
        }

        Obj *var = new_lvar("", ty);
        Node *lhs = lvar_initializer(rest, tok, var);
        Node *rhs = new_var_node(var, tok);
        return new_binary(ND_COMMA, lhs, rhs, start);
    }

    Node *node = primary(&tok, tok);
    for (;;)
    {
        if (equal(tok, "("))
        {
            node = funccall(&tok, tok->next, node);
            continue;
        }
        if (equal(tok, "["))
        {
            // x[y] is short for *(x+y)
            Token *start = tok;
            Node *idx = expr(&tok, tok->next);
            tok = skip(tok, "]");
            node = new_unary(ND_DEREF, new_add(node, idx, start), start);
            continue;
        }
        if (equal(tok, "++"))
        {
            node = new_inc_dec(node, tok, 1);
            tok = tok->next;
            continue;
        }
        if (equal(tok, "--"))
        {
            node = new_inc_dec(node, tok, -1);
            tok = tok->next;
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
            node = struct_ref(tok->next, node);
            tok = tok->next->next;
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
static Node *cast(Token **rest, Token *tok)
{
    if (equal(tok, "(") && is_typename(tok->next))
    {
        Token *start = tok;
        tok = tok->next;
        Type *ty = typename(&tok, tok);
        tok = skip(tok, ")");

        // compound literal
        if (equal(tok, "{"))
        {
            return unary(rest, start);
        }

        // type cast
        Node *node = new_cast(cast(&tok, tok), ty);
        node->tok = start;
        *rest = tok;
        return node;
    }
    return unary(rest, tok);
}

// unary = ("+" | "-" | "&" | "*" | "!" | "~") cast
//       | ("++" | "--") unary
//       | postfix
static Node *unary(Token **rest, Token *tok)
{
    if (equal(tok, "+"))
    {
        Node *node = cast(&tok, tok->next);
        *rest = tok;
        return node;
    }

    if (equal(tok, "!"))
    {
        Node *node = new_unary(ND_NOT, cast(&tok, tok->next), tok);
        *rest = tok;
        return node;
    }

    if (equal(tok, "~"))
    {
        Node *node = new_unary(ND_BITNOT, cast(&tok, tok->next), tok);
        *rest = tok;
        return node;
    }

    if (equal(tok, "-"))
    {
        Node *node = new_unary(ND_NEG, cast(&tok, tok->next), tok);
        *rest = tok;
        return node;
    }

    if (equal(tok, "++"))
    {
        Node *node = to_assign(new_add(unary(&tok, tok->next), new_num(1, tok), tok));
        *rest = tok;
        return node;
    }

    if (equal(tok, "--"))
    {
        Node *node = to_assign(new_sub(unary(&tok, tok->next), new_num(1, tok), tok));
        *rest = tok;
        return node;
    }

    if (equal(tok, "&"))
    {
        Node *lhs = cast(rest, tok->next);
        add_type(lhs);
        if (lhs->kind == ND_MEMBER && lhs->member->is_bitfield)
        {
            error_tok(tok, "cannot take address of bitfield");
        }
        return new_unary(ND_ADDR, lhs, tok);
    }

    if (equal(tok, "*"))
    {
        // [https://www.sigbus.info/n1570#6.5.3.2p4] This is an oddity
        // in the C spec, but dereferencing a function shouldn't do
        // anything. If foo is a function, `*foo`, `**foo` or `*****foo`
        // are all equivalent to just `foo`.
        Node *node = cast(rest, tok->next);
        add_type(node);
        if (node->ty->kind == TY_FUNC)
        {
            return node;
        }
        return new_unary(ND_DEREF, node, tok);
    }

    return postfix(rest, tok);
}

// mul = cast ("*" cast | "/" cast | "%" cast)*
static Node *mul(Token **rest, Token *tok)
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

        if (equal(tok, "%"))
        {
            node = new_binary(ND_MOD, node, cast(&tok, tok->next), start);
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
static Node *new_add(Node *lhs, Node *rhs, Token *tok)
{
    add_type(lhs);
    add_type(rhs);

    // num + num
    if (is_numeric(lhs->ty) && is_numeric(rhs->ty))
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
    if (is_numeric(lhs->ty) && is_numeric(rhs->ty))
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
        node->ty = ty_long;
        return new_binary(ND_DIV, node, new_num(lhs->ty->base->size, tok), tok);
    }

    error_tok(tok, "invalid operands");
}

// add = mul ("+" mul | "-" mul)*
static Node *add(Token **rest, Token *tok)
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

// shift = add ( ">>" add | "<<" add)*
Node *shift(Token **rest, Token *tok)
{
    Node *node = add(&tok, tok);
    for (;;)
    {
        if (equal(tok, ">>"))
        {
            node = new_binary(ND_SHR, node, add(&tok, tok->next), tok);
            continue;
        }
        if (equal(tok, "<<"))
        {
            node = new_binary(ND_SHL, node, add(&tok, tok->next), tok);
            continue;
        }
        *rest = tok;
        return node;
    }
}

// relational = shift ("<" shift | "<=" shift | ">" shift | ">=" shift)*
static Node *relational(Token **rest, Token *tok)
{
    Node *node = shift(&tok, tok);

    for (;;)
    {
        Token *start = tok;
        if (equal(tok, "<"))
        {
            node = new_binary(ND_LT, node, shift(&tok, tok->next), tok);
            continue;
        }

        if (equal(tok, "<="))
        {
            node = new_binary(ND_LE, node, shift(&tok, tok->next), tok);
            continue;
        }

        if (equal(tok, ">"))
        {
            node = new_binary(ND_LT, shift(&tok, tok->next), node, tok);
            continue;
        }

        if (equal(tok, ">="))
        {
            node = new_binary(ND_LE, shift(&tok, tok->next), node, tok);
            continue;
        }

        *rest = tok;
        return node;
    }
}

// equality = relational ("==" relational | "!=" relational)*
static Node *equality(Token **rest, Token *tok)
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

// bitand = equality ("&" bitand)*
static Node *bitand(Token **rest, Token *tok)
{
    Node *node = equality(&tok, tok);
    while (equal(tok, "&"))
    {
        Token *start = tok;
        node = new_binary(ND_BITAND, node, bitand(&tok, tok->next), start);
    }
    *rest = tok;
    return node;
}

// bitxor = bitand ("^" bitxor)*
static Node *bitxor(Token **rest, Token *tok)
{
    Node *node = bitand(&tok, tok);
    while (equal(tok, "^"))
    {
        Token *start = tok;
        node = new_binary(ND_BITXOR, node, bitxor(&tok, tok->next), start);
    }
    *rest = tok;
    return node;
}

// bitor = bitxor ("|" bitor)*
static Node * bitor (Token * *rest, Token *tok)
{
    Node *node = bitxor(&tok, tok);
    while (equal(tok, "|"))
    {
        Token *start = tok;
        node = new_binary(ND_BITOR, node, bitor (&tok, tok->next), start);
    }
    *rest = tok;
    return node;
}

// logand = bitor ("||" logand)*
static Node *logand(Token **rest, Token *tok)
{
    Node *node = bitor (&tok, tok);
    while (equal(tok, "&&"))
    {
        Token *start = tok;
        node = new_binary(ND_LOGAND, node, logand(&tok, tok->next), start);
    }
    *rest = tok;
    return node;
}

// logor = logand ("||" logor)*
static Node *logor(Token **rest, Token *tok)
{
    Node *node = logand(&tok, tok);
    while (equal(tok, "||"))
    {
        Token *start = tok;
        node = new_binary(ND_LOGOR, node, logor(&tok, tok->next), start);
    }
    *rest = tok;
    return node;
}

// Evaluate a given node as a constant expression.
static int64_t eval(Node *node)
{
    return eval2(node, NULL);
}

static double eval_double(Node *node)
{
    add_type(node);

    if (is_integer(node->ty))
    {
        if (node->ty->is_unsigned)
            return (unsigned long)eval(node);
        return eval(node);
    }

    switch (node->kind)
    {
    case ND_ADD:
        return eval_double(node->lhs) + eval_double(node->rhs);
    case ND_SUB:
        return eval_double(node->lhs) - eval_double(node->rhs);
    case ND_MUL:
        return eval_double(node->lhs) * eval_double(node->rhs);
    case ND_DIV:
        return eval_double(node->lhs) / eval_double(node->rhs);
    case ND_NEG:
        return -eval_double(node->lhs);
    case ND_COND:
        return eval_double(node->cond) ? eval_double(node->then) : eval_double(node->els);
    case ND_COMMA:
        return eval_double(node->rhs);
    case ND_CAST:
        if (is_flonum(node->lhs->ty))
        {
            return eval_double(node->lhs);
        }
        return eval(node->lhs);
    case ND_NUM:
        return node->fval;
    }

    error_tok(node->tok, "not a compile-time constant");
}

// Evaluate a given node as a constant expression.
//
// A constant expression is either just a number or ptr+n where ptr
// is a pointer to a global variable and n is a postiive/negative
// number. The latter form is accepted only as an initialization
// expression for a global variable.
static int64_t eval2(Node *node, char **label)
{
    add_type(node);

    if (is_flonum(node->ty))
    {
        return eval_double(node);
    }

    switch (node->kind)
    {
    case ND_ADD:
        return eval2(node->lhs, label) + eval(node->rhs);
    case ND_SUB:
        return eval2(node->lhs, label) - eval(node->rhs);
    case ND_MUL:
        return eval(node->lhs) * eval(node->rhs);
    case ND_DIV:
        if (node->ty->is_unsigned)
        {
            return (uint64_t)eval(node->lhs) / eval(node->rhs);
        }
        return eval(node->lhs) / eval(node->rhs);
    case ND_NEG:
        return -eval(node->lhs);
    case ND_MOD:
        if (node->ty->is_unsigned)
        {
            return (uint64_t)eval(node->lhs) % eval(node->rhs);
        }
        return eval(node->lhs) % eval(node->rhs);
    case ND_BITAND:
        return eval(node->lhs) & eval(node->rhs);
    case ND_BITOR:
        return eval(node->lhs) | eval(node->rhs);
    case ND_BITXOR:
        return eval(node->lhs) ^ eval(node->rhs);
    case ND_SHL:
        return eval(node->lhs) << eval(node->rhs);
    case ND_SHR:
        if (node->ty->is_unsigned && node->ty->size == 8)
        {
            return (uint64_t)eval(node->lhs) >> eval(node->rhs);
        }
        return eval(node->lhs) >> eval(node->rhs);
    case ND_EQ:
        return eval(node->lhs) == eval(node->rhs);
    case ND_NE:
        return eval(node->lhs) != eval(node->rhs);
    case ND_LT:
        if (node->lhs->ty->is_unsigned)
        {
            return (uint64_t)eval(node->lhs) < eval(node->rhs);
        }
        return eval(node->lhs) < eval(node->rhs);
    case ND_LE:
        if (node->lhs->ty->is_unsigned)
        {
            return (uint64_t)eval(node->lhs) <= eval(node->rhs);
        }
        return eval(node->lhs) <= eval(node->rhs);
    case ND_COND:
        return eval(node->cond) ? eval2(node->then, label) : eval2(node->els, label);
    case ND_COMMA:
        return eval2(node->rhs, label);
    case ND_NOT:
        return !eval(node->lhs);
    case ND_BITNOT:
        return ~eval(node->lhs);
    case ND_LOGAND:
        return eval(node->lhs) && eval(node->rhs);
    case ND_LOGOR:
        return eval(node->lhs) || eval(node->rhs);
    case ND_CAST:
    {
        int64_t val = eval2(node->lhs, label);
        if (is_integer(node->ty))
        {
            switch (node->ty->size)
            {
            case 1:
            {
                return node->ty->is_unsigned ? (uint8_t)val : (int8_t)val;
            }
            case 2:
            {
                return node->ty->is_unsigned ? (uint16_t)val : (int16_t)val;
            }
            case 4:
            {
                return node->ty->is_unsigned ? (uint32_t)val : (int32_t)val;
            }
            }
        }
        return val;
    }
    case ND_ADDR:
    {
        return eval_rval(node->lhs, label);
    }
    case ND_MEMBER:
    {
        if (!label)
        {
            error_tok(node->tok, "not a compile-time constant");
        }
        if (node->ty->kind != TY_ARRAY)
        {
            error_tok(node->tok, "invalid initializer");
        }
        return eval_rval(node->lhs, label) + node->member->offset;
    }
    case ND_VAR:
        if (!label)
        {
            error_tok(node->tok, "not a compile-time constant");
        }
        if (node->var->ty->kind != TY_ARRAY && node->var->ty->kind != TY_FUNC)
        {
            error_tok(node->tok, "invalid initializer");
        }
        *label = node->var->name;
        return 0;
    case ND_NUM:
        return node->val;
    }
    error_tok(node->tok, "not a compile-time constant");
}

static int64_t eval_rval(Node *node, char **label)
{
    switch (node->kind)
    {
    case ND_VAR:
    {
        if (node->var->is_local)
        {
            error_tok(node->tok, "not a compile-time constant");
        }
        *label = node->var->name;
        return 0;
    }
    case ND_DEREF:
    {
        return eval2(node->lhs, label);
    }
    case ND_MEMBER:
    {
        return eval_rval(node->lhs, label) + node->member->offset;
    }
    }
    error_tok(node->tok, "invalid initializer");
}

int64_t const_expr(Token **rest, Token *tok)
{
    Node *node = conditional(rest, tok);
    return eval(node);
}

// conditional = logor ("?" expr? ":" conditional)?
static Node *conditional(Token **rest, Token *tok)
{
    Node *cond = logor(&tok, tok);
    if (!equal(tok, "?"))
    {
        *rest = tok;
        return cond;
    }

    if (equal(tok->next, ":"))
    {
        // [GNU] Compile `a ?: b` as `tmp = a, tmp ? tmp : b`.
        add_type(cond);
        Obj *var = new_lvar("", cond->ty);
        Node *lhs = new_binary(ND_ASSIGN, new_var_node(var, tok), cond, tok);
        Node *rhs = new_node(ND_COND, tok);
        rhs->cond = new_var_node(var, tok);
        rhs->then = new_var_node(var, tok);
        rhs->els = conditional(rest, tok->next->next);
        return new_binary(ND_COMMA, lhs, rhs, tok);
    }

    Node *node = new_node(ND_COND, tok);
    node->cond = cond;
    node->then = expr(&tok, tok->next);
    tok = skip(tok, ":");
    node->els = conditional(&tok, tok);
    *rest = tok;
    return node;
}

// assign = conditional (assign-op assign)?
// assign-op = "=" | "+=" | "-=" | "*=" | "/=" | "%=" | "|=" | "^=" | "&=" | "<<=" | ">>="
static Node *assign(Token **rest, Token *tok)
{
    Node *node = conditional(&tok, tok);
    if (equal(tok, "="))
    {
        Node *rhs = assign(&tok, tok->next);
        node = new_binary(ND_ASSIGN, node, rhs, tok);
    }
    if (equal(tok, "+="))
    {
        node = to_assign(new_add(node, assign(&tok, tok->next), tok));
    }

    if (equal(tok, "-="))
    {
        node = to_assign(new_sub(node, assign(&tok, tok->next), tok));
    }

    if (equal(tok, "*="))
    {
        node = to_assign(new_binary(ND_MUL, node, assign(&tok, tok->next), tok));
    }

    if (equal(tok, "/="))
    {
        node = to_assign(new_binary(ND_DIV, node, assign(&tok, tok->next), tok));
    }

    if (equal(tok, "%="))
    {
        node = to_assign(new_binary(ND_MOD, node, assign(&tok, tok->next), tok));
    }

    if (equal(tok, "|="))
    {
        node = to_assign(new_binary(ND_BITOR, node, assign(&tok, tok->next), tok));
    }

    if (equal(tok, "&="))
    {
        node = to_assign(new_binary(ND_BITAND, node, assign(&tok, tok->next), tok));
    }

    if (equal(tok, "^="))
    {
        node = to_assign(new_binary(ND_BITXOR, node, assign(&tok, tok->next), tok));
    }

    if (equal(tok, "<<="))
    {
        node = to_assign(new_binary(ND_SHL, node, assign(&tok, tok->next), tok));
    }

    if (equal(tok, ">>="))
    {
        node = to_assign(new_binary(ND_SHR, node, assign(&tok, tok->next), tok));
    }

    *rest = tok;
    return node;
}

// expr = assign ("," expr)?
static Node *expr(Token **rest, Token *tok)
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
static void struct_members(Token **rest, Token *tok, Type *ty)
{
    Member head = {};
    Member *cur = &head;
    int idx = 0;
    while (!equal(tok, "}"))
    {
        bool first = true;
        VarAttr attr = {};
        Type *basety = declspec(&tok, tok, &attr);

        // Anonymous struct member
        if ((basety->kind == TY_STRUCT || basety->kind == TY_UNION) &&
            consume(&tok, tok, ";"))
        {
            Member *mem = calloc(1, sizeof(Member));
            mem->ty = basety;
            mem->idx = idx++;
            mem->align = attr.align ? attr.align : mem->ty->align;
            cur = cur->next = mem;
            continue;
        }

        // Regular struct members
        while (!equal(tok, ";"))
        {
            if (!first)
            {
                tok = skip(tok, ",");
            }
            first = false;

            Member *mem = calloc(1, sizeof(Member));
            mem->ty = declarator(&tok, tok, basety);
            mem->name = mem->ty->name;
            mem->idx = idx++;
            mem->align = attr.align ? attr.align : mem->ty->align;

            if (consume(&tok, tok, ":"))
            {
                mem->is_bitfield = true;
                mem->bit_width = const_expr(&tok, tok);
            }
            cur = cur->next = mem;
        }
        tok = skip(tok, ";");
    }

    // If the last element is an array of incomplete type, it's
    // called a "flexible array member". It should behave as if
    // if were a zero-sized array.
    if (cur != &head && cur->ty->kind == TY_ARRAY && cur->ty->array_len < 0)
    {
        cur->ty = array_of(cur->ty->base, 0);
        ty->is_flexible = true;
    }

    *rest = tok->next;
    ty->members = head.next;
}

// struct-union-decl = ident? ("{" struct-members )
//                    | ident ("{" struct-members )?
static Type *struct_union_decl(Token **rest, Token *tok)
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
        if (ty)
        {
            *rest = tok;
            return ty;
        }

        ty = struct_type();
        ty->size = -1;
        push_tag_scope(tag, ty);
        *rest = tok;
        return ty;
    }

    tok = skip(tok, "{");

    Type *ty = struct_type();
    struct_members(&tok, tok, ty);
    *rest = tok;

    if (tag)
    {
        // If this is a redefinition, overwrite a previous type.
        // Otherwise, register the struct type.
        for (TagScope *sc = scope->tags; sc; sc = sc->next)
        {
            if (equal(tag, sc->name))
            {
                *sc->ty = *ty;
                return sc->ty;
            }
        }
        push_tag_scope(tag, ty);
    }
    return ty;
}

static Type *struct_decl(Token **rest, Token *tok)
{
    Type *ty = struct_union_decl(&tok, tok);
    ty->kind = TY_STRUCT;
    if (ty->size < 0)
    {
        *rest = tok;
        return ty;
    }

    // Assign offsets within the struct to members.
    int bits = 0;
    for (Member *mem = ty->members; mem; mem = mem->next)
    {

        if (mem->is_bitfield && mem->bit_width == 0)
        {
            // Zero-width anonymous bitfield has a special meaning.
            // It affects only alignment.
            bits = align_to(bits, mem->ty->size * 8);
        }
        else if (mem->is_bitfield)
        {
            int sz = mem->ty->size;
            if (bits / (sz * 8) != (bits + mem->bit_width - 1) / (sz * 8))
            {
                bits = align_to(bits, sz * 8);
            }

            mem->offset = align_down(bits / 8, sz);
            mem->bit_offset = bits % (sz * 8);
            bits += mem->bit_width;
        }
        else
        {
            bits = align_to(bits, mem->align * 8);
            mem->offset = bits / 8;
            bits += mem->ty->size * 8;
        }
        if (ty->align < mem->align)
        {
            ty->align = mem->align;
        }
    }

    ty->size = align_to(bits, ty->align * 8) / 8;
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
        if (ty->align < mem->align)
        {
            ty->align = mem->align;
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

static bool is_end(Token *tok)
{
    return equal(tok, "}") || (equal(tok, ",") && equal(tok->next, "}"));
}

static bool consume_end(Token **rest, Token *tok)
{
    if (equal(tok, "}"))
    {
        *rest = tok->next;
        return true;
    }

    if (equal(tok, ",") && equal(tok->next, "}"))
    {
        *rest = tok->next->next;
        return true;
    }

    return false;
}

// typeof-specifier = "(" (expr | typename) ")"
static Type *typeof_specifier(Token **rest, Token *tok)
{
    tok = skip(tok, "(");

    Type *ty;
    if (is_typename(tok))
    {
        ty = typename(&tok, tok);
    }
    else
    {
        Node *node = expr(&tok, tok);
        add_type(node);
        ty = node->ty;
    }
    *rest = skip(tok, ")");
    return ty;
}

// enum-specifier = ident? "{" enum-list? "}"
//                | ident ("{" enum-list? "}")?
// enum-list      = ident ("=" num)? ("," ident ("=" num)?)*
static Type *enum_specifier(Token **rest, Token *tok)
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
    while (!consume_end(rest, tok))
    {
        if (i++ > 0)
        {
            tok = skip(tok, ",");
        }
        char *name = get_ident(tok);
        tok = tok->next;

        if (equal(tok, "="))
        {
            val = const_expr(&tok, tok->next);
        }
        VarScope *vs = push_scope(name);
        vs->enum_ty = ty;
        vs->enum_val = val++;
    }

    if (tag)
    {
        push_tag_scope(tag, ty);
    }
    return ty;
}

// declspec = ( "void" | "int" | "char" | _Bool | "long"
//                  | "signed" | "unsigned"
//                  | "typedef" | "static" | "extern" | inline
//                  | struct-decl | union_decl  | typedef-name
//                  | enum-specifier | typeof-specifier
//                  | "const" | "volatile" | "auto" | "register" | "restrict"
//                  | "__restrict" | "__restrict__" | "_Noreturn")+
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
static Type *declspec(Token **rest, Token *tok, VarAttr *attr)
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
        FLOAT = 1 << 12,
        DOUBLE = 1 << 14,
        OTHER = 1 << 16,
        SIGNED = 1 << 17,
        UNSIGNED = 1 << 18,
    };

    Type *ty = ty_int;
    int counter = 0;

    while (is_typename(tok))
    {
        if (equal(tok, "typedef") || equal(tok, "static") ||
            equal(tok, "extern") || equal(tok, "inline"))
        {
            if (!attr)
            {
                error_tok(tok, "storage class specifier is not allowed in this context");
            }
            if (equal(tok, "typedef"))
            {
                attr->is_typedef = true;
            }
            else if (equal(tok, "static"))
            {
                attr->is_static = true;
            }
            else if (equal(tok, "extern"))
            {
                attr->is_extern = true;
            }
            else
            {
                attr->is_inline = true;
            }

            if (attr->is_typedef && attr->is_static + attr->is_extern + attr->is_inline > 1)
            {
                error_tok(tok, "typedef may not be used together with static, extern or inline");
            }
            tok = tok->next;
            continue;
        }

        // These keywords are recognized but ignored.
        if (consume(&tok, tok, "const") || consume(&tok, tok, "volatile") ||
            consume(&tok, tok, "auto") || consume(&tok, tok, "register") ||
            consume(&tok, tok, "restrict") || consume(&tok, tok, "__restrict") ||
            consume(&tok, tok, "__restrict__") || consume(&tok, tok, "_Noreturn"))
        {
            continue;
        }

        if (equal(tok, "_Alignas"))
        {
            if (!attr)
            {
                error_tok(tok, "_Alignas is not allowed in this context");
            }
            tok = skip(tok->next, "(");

            if (is_typename(tok))
            {
                attr->align = typename(&tok, tok)->align;
            }
            else
            {
                attr->align = const_expr(&tok, tok);
            }
            tok = skip(tok, ")");
            continue;
        }

        Type *ty2 = find_typedef(tok);
        if (equal(tok, "struct") || equal(tok, "union") || equal(tok, "enum") ||
            equal(tok, "typeof") || ty2)
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
            else if (equal(tok, "typeof"))
            {
                ty = typeof_specifier(&tok, tok->next);
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
        else if (equal(tok, "float"))
        {
            counter += FLOAT;
        }
        else if (equal(tok, "double"))
        {
            counter += DOUBLE;
        }
        else if (equal(tok, "signed"))
        {
            counter |= SIGNED;
        }
        else if (equal(tok, "unsigned"))
        {
            counter |= UNSIGNED;
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
        case SIGNED + CHAR:
            ty = ty_char;
            break;
        case UNSIGNED + CHAR:
            ty = ty_uchar;
            break;
        case SHORT:
        case SHORT + INT:
        case SIGNED + SHORT:
        case SIGNED + SHORT + INT:
            ty = ty_short;
            break;
        case UNSIGNED + SHORT:
        case UNSIGNED + SHORT + INT:
            ty = ty_ushort;
            break;
        case INT:
        case SIGNED:
        case SIGNED + INT:
            ty = ty_int;
            break;
        case UNSIGNED:
        case UNSIGNED + INT:
            ty = ty_uint;
            break;
        case LONG:
        case LONG + INT:
        case LONG + LONG:
        case LONG + LONG + INT:
        case SIGNED + LONG:
        case SIGNED + LONG + INT:
        case SIGNED + LONG + LONG:
        case SIGNED + LONG + LONG + INT:
            ty = ty_long;
            break;
        case UNSIGNED + LONG:
        case UNSIGNED + LONG + INT:
        case UNSIGNED + LONG + LONG:
        case UNSIGNED + LONG + LONG + INT:
            ty = ty_ulong;
            break;
        case FLOAT:
            ty = ty_float;
            break;
        case DOUBLE:
        case LONG + DOUBLE:
            ty = ty_double;
            break;
        default:
            error_tok(tok, "invalid type");
        }
        tok = tok->next;
    }

    *rest = tok;
    return ty;
}

// func-params = ("void" | param ("," param)* (",", "...")?)?
// param = declspec declarator
static Type *func_params(Token **rest, Token *tok, Type *ty)
{
    if (equal(tok, "void") && equal(tok->next, ")"))
    {
        *rest = tok->next;
        return func_type(ty);
    }
    Type head = {};
    Type *cur = &head;
    bool is_variadic = false;
    int i = 0;
    while (!equal(tok, ")"))
    {
        if (i++ > 0)
        {
            tok = skip(tok, ",");
        }
        if (equal(tok, "..."))
        {
            tok = tok->next;
            is_variadic = true;
            break;
        }
        Type *ty2 = declspec(&tok, tok, NULL);
        ty2 = declarator(&tok, tok, ty2);

        Token *name = ty2->name;
        if (ty2->kind == TY_ARRAY)
        {
            // "array of T" is converted to "pointer to T" only in the parameter
            // context. For example, *argv[] is converted to **argv by this.
            ty2 = pointer_to(ty2->base);
            ty2->name = name;
        }
        else if (ty2->kind == TY_FUNC)
        {
            // Likewise, a function is converted to a pointer to a function
            // only in the parameter context.
            ty2 = pointer_to(ty2);
            ty2->name = name;
        }

        cur = cur->next = copy_type(ty2);
    }
    ty = func_type(ty);
    ty->is_variadic = is_variadic;
    ty->params = head.next;
    *rest = tok;
    return ty;
}

// array-dimensions = ("static" | "restrict")*  const-expr? "]" type-suffix
static Type *array_dimensions(Token **rest, Token *tok, Type *ty)
{
    while (equal(tok, "static") || equal(tok, "restrict"))
    {
        tok = tok->next;
    }

    if (equal(tok, "]"))
    {
        tok = tok->next;
        ty = type_suffix(&tok, tok, ty);
        *rest = tok;
        return array_of(ty, -1);
    }

    int len = const_expr(&tok, tok);
    tok = skip(tok, "]");
    ty = type_suffix(&tok, tok, ty);
    *rest = tok;
    return array_of(ty, len);
}

// type-suffix = ("(" func-params? ")")?
//               | "[" array-dimensions
static Type *type_suffix(Token **rest, Token *tok, Type *ty)
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
        ty = array_dimensions(&tok, tok, ty);
        *rest = tok;
        return ty;
    }
    *rest = tok;
    return ty;
}

// abstract-declarator = "*"* ("(" abstract-declarator ")")? type-suffix
static Type *abstract_declarator(Token **rest, Token *tok, Type *ty)
{
    ty = pointers(&tok, tok, ty);

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

static Type *typename(Token **rest, Token *tok)
{
    Type *basety = declspec(&tok, tok, NULL);
    Type *ty = abstract_declarator(&tok, tok, basety);
    *rest = tok;
    return ty;
}

// pointers = ("*" ("const" | "volatile" | "restrict")*)*
static Type *pointers(Token **rest, Token *tok, Type *ty)
{
    while (consume(&tok, tok, "*"))
    {
        ty = pointer_to(ty);
        while (equal(tok, "const") || equal(tok, "volatile") || equal(tok, "restrict") ||
               equal(tok, "__restrict") || equal(tok, "__restrict__"))
            tok = tok->next;
    }
    *rest = tok;
    return ty;
}

// declarator = pointers ("(" ident ")" | "(" declarator ")" | ident) type-suffix
static Type *declarator(Token **rest, Token *tok, Type *ty)
{
    ty = pointers(&tok, tok, ty);

    if (equal(tok, "("))
    {
        Token *start = tok;
        Type dummy = {};
        declarator(&tok, start->next, &dummy);
        tok = skip(tok, ")");
        ty = type_suffix(rest, tok, ty);
        return declarator(&tok, start->next, ty);
    }

    Token *name = NULL;
    Token *name_pos = tok;
    if (tok->kind == TK_IDENT)
    {
        name = tok;
        tok = tok->next;
    }
    ty = type_suffix(rest, tok, ty);
    ty->name = name;
    ty->name_pos = name_pos;
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

static Initializer *new_initializer(Type *ty, Obj *var, bool is_flexible)
{
    Initializer *init = calloc(1, sizeof(Initializer));
    init->ty = ty;
    init->var = var;

    if (ty->kind == TY_ARRAY)
    {
        if (is_flexible && ty->size < 0)
        {
            init->is_flexible = true;
            return init;
        }
        init->children = calloc(ty->array_len, sizeof(Initializer *));
        for (int i = 0; i < ty->array_len; i++)
        {
            Initializer *init2 = new_initializer(ty->base, NULL, false);
            init2->idx = i;
            init2->next = init;
            init->children[i] = init2;
        }
        return init;
    }

    if (ty->kind == TY_STRUCT || ty->kind == TY_UNION)
    {
        int len = 0;
        for (Member *mem = ty->members; mem; mem = mem->next)
        {
            len++;
        }

        init->children = calloc(len, sizeof(Initializer *));
        for (Member *mem = ty->members; mem; mem = mem->next)
        {
            if (is_flexible && ty->is_flexible && !mem->next)
            {
                Initializer *child = calloc(1, sizeof(Initializer));
                child->is_flexible = true;
                child->ty = mem->ty;
                child->idx = mem->idx;
                child->mem = mem;
                child->next = init;
                init->children[mem->idx] = child;
            }
            else
            {
                Initializer *init2 = new_initializer(mem->ty, NULL, false);
                init2->ty = mem->ty;
                init2->idx = mem->idx;
                init2->mem = mem;
                init2->next = init;
                init->children[mem->idx] = init2;
            }
        }
        return init;
    }
    return init;
}

static Token *skip_excess_element(Token *tok)
{
    if (equal(tok, "{"))
    {
        tok = skip_excess_element(tok->next);
        return skip(tok, "}");
    }
    assign(&tok, tok);
    return tok;
}

static int count_array_init_elements(Token *tok, Type *ty)
{
    bool first = true;
    Initializer *dummy = new_initializer(ty->base, NULL, false);
    int i = 0, max = 0;

    while (!consume_end(&tok, tok))
    {
        if (!first)
        {
            tok = skip(tok, ",");
        }
        first = false;
        if (equal(tok, "["))
        {
            i = const_expr(&tok, tok->next);
            if (equal(tok, "..."))
            {
                i = const_expr(&tok, tok->next);
            }
            tok = skip(tok, "]");
            designation(&tok, tok, dummy);
        }
        else
        {
            initializer2(&tok, tok, dummy);
        }
        i++;
        max = MAX(max, i);
    }
    return max;
}

// array-initializer2 = initializer ("," initializer)*
static void array_initializer2(Token **rest, Token *tok, Initializer *init, int i)
{
    if (init->is_flexible)
    {
        int len = count_array_init_elements(tok, init->ty);
        Type *ty = array_of(init->ty->base, len);
        if (init->var)
        {
            init->var->ty = ty;
        }
        *init = *new_initializer(ty, init->var, false);
    }

    for (; i < init->ty->array_len && !is_end(tok); i++)
    {
        Token *start = tok;
        if (i > 0)
        {
            tok = skip(tok, ",");
        }
        if (equal(tok, "[") || equal(tok, "."))
        {
            *rest = start;
            return;
        }
        initializer2(&tok, tok, init->children[i]);
    }
    *rest = tok;
    return;
}

// array-designator = "[" const-expr "]"
//
// C99 added the designated initializer to the language, which allows
// programmers to move the "cursor" of an initializer to any element.
// The syntax looks like this:
//
//   int x[10] = { 1, 2, [5]=3, 4, 5, 6, 7 };
//
// `[5]` moves the cursor to the 5th element, so the 5th element of x
// is set to 3. Initialization then continues forward in order, so
// 6th, 7th, 8th and 9th elements are initialized with 4, 5, 6 and 7,
// respectively. Unspecified elements (in this case, 3rd and 4th
// elements) are initialized with zero.
//
// Nesting is allowed, so the following initializer is valid:
//
//   int x[5][10] = { [5][8]=1, 2, 3 };
//
// It sets x[5][8], x[5][9] and x[6][0] to 1, 2 and 3, respectively.
static int array_designator(Token **rest, Token *tok, Type *ty)
{
    Token *start = tok;
    int i = const_expr(&tok, tok->next);
    if (i >= ty->array_len)
    {
        error_tok(start, "array designator index exceeds array bounds");
    }
    *rest = skip(tok, "]");
    return i;
}

// struct-designator = "." ident
static Member *struct_designator(Token **rest, Token *tok, Type *ty)
{
    Token *start = tok;
    tok = tok->next;
    if (tok->kind != TK_IDENT)
    {
        error_tok(tok, "expected a field designator");
    }

    for (Member *mem = ty->members; mem; mem = mem->next)
    {
        // Anonymous struct member
        if (mem->ty->kind == TY_STRUCT && !mem->name)
        {
            if (get_struct_member(mem->ty, tok))
            {
                *rest = start;
                return mem;
            }
            continue;
        }

        // Regular struct member
        if (mem->name->len == tok->len && !strncmp(mem->name->loc, tok->loc, tok->len))
        {
            *rest = tok->next;
            return mem;
        }
    }
    error_tok(tok, "struct has no such member");
}

// designation = ("[" const-expr "]" | "." ident)* "="? initializer
static void designation(Token **rest, Token *tok, Initializer *init)
{
    if (equal(tok, "["))
    {
        if (init->ty->kind != TY_ARRAY)
        {
            error_tok(tok, "array index in non-array initializer");
        }
        int i = array_designator(&tok, tok, init->ty);
        designation(&tok, tok, init->children[i]);
        array_initializer2(rest, tok, init, i + 1);
        return;
    }

    if (equal(tok, ".") && init->ty->kind == TY_STRUCT)
    {
        Member *mem = struct_designator(&tok, tok, init->ty);
        designation(&tok, tok, init->children[mem->idx]);
        // designation may reassign value, so we should rest it.
        init->expr = NULL;
        struct_initializer2(rest, tok, init, mem->next);
        return;
    }

    if (equal(tok, ".") && init->ty->kind == TY_UNION)
    {
        Member *mem = struct_designator(&tok, tok, init->ty);
        init->mem = mem;
        designation(&tok, tok, init->children[mem->idx]);
        return;
    }

    if (equal(tok, "."))
    {
        error_tok(tok, "field name not in struct or union initializer");
    }

    if (equal(tok, "="))
    {
        tok = tok->next;
    }
    initializer2(rest, tok, init);
}

// array-initializer1 = "{" initializer ("," initializer)* "}"
static void array_initializer1(Token **rest, Token *tok, Initializer *init)
{
    tok = skip(tok, "{");
    bool first = true;

    if (init->is_flexible)
    {
        int len = count_array_init_elements(tok, init->ty);
        Type *ty = array_of(init->ty->base, len);
        if (init->var)
        {
            init->var->ty = ty;
        }
        *init = *new_initializer(ty, init->var, false);
    }

    for (int i = 0; !consume_end(rest, tok); i++)
    {
        if (!first)
        {
            tok = skip(tok, ",");
        }
        first = false;

        if (equal(tok, "["))
        {
            i = array_designator(&tok, tok, init->ty);
            designation(&tok, tok, init->children[i]);
            continue;
        }

        if (i < init->ty->array_len)
        {
            initializer2(&tok, tok, init->children[i]);
        }
        else
        {
            tok = skip_excess_element(tok);
        }
    }
    return;
}

static void string_initializer(Token **rest, Token *tok, Initializer *init)
{
    if (init->is_flexible)
    {
        Type *ty = array_of(init->ty->base, tok->ty->array_len);
        init->var->ty = ty;
        *init = *new_initializer(ty, init->var, false);
    }

    int len = MIN(init->ty->array_len, tok->ty->array_len);
    switch (init->ty->base->size)
    {
    case 1:
    {
        char *str = tok->str;
        for (int i = 0; i < len; i++)
        {
            init->children[i]->expr = new_num(str[i], tok);
        }
        break;
    }
    case 2:
    {
        uint16_t *str = (uint16_t *)tok->str;
        for (int i = 0; i < len; i++)
        {
            init->children[i]->expr = new_num(str[i], tok);
        }
        break;
    }
    case 4:
    {
        uint32_t *str = (uint32_t *)tok->str;
        for (int i = 0; i < len; i++)
        {
            init->children[i]->expr = new_num(str[i], tok);
        }
        break;
    }
    default:
        unreachable();
    }
    *rest = tok->next;
    return;
}

// struct-initializer1 = "{" initializer ("," initializer)* "}"
static void struct_initializer1(Token **rest, Token *tok, Initializer *init)
{
    tok = skip(tok, "{");

    Member *mem = init->ty->members;
    bool first = true;
    while (!consume_end(rest, tok))
    {
        if (!first)
        {
            tok = skip(tok, ",");
        }
        first = false;

        if (equal(tok, "."))
        {
            mem = struct_designator(&tok, tok, init->ty);
            designation(&tok, tok, init->children[mem->idx]);
            mem = mem->next;
            continue;
        }

        if (mem)
        {
            initializer2(&tok, tok, init->children[mem->idx]);
            mem = mem->next;
        }
        else
        {
            tok = skip_excess_element(tok);
        }
    }
    return;
}

// struct-initializer2 =  initializer ("," initializer)*
static void struct_initializer2(Token **rest, Token *tok, Initializer *init, Member *mem)
{
    bool first = true;
    for (; mem && !is_end(tok); mem = mem->next)
    {
        Token *start = tok;
        if (!first)
        {
            tok = skip(tok, ",");
        }
        first = false;

        if (equal(tok, "[") || equal(tok, "."))
        {
            *rest = start;
            return;
        }
        initializer2(&tok, tok, init->children[mem->idx]);
    }
    *rest = tok;
    return;
}

static void union_initializer(Token **rest, Token *tok, Initializer *init)
{
    // Unlike structs, union initializers take only one initializer,
    // and that initializes the first union member by default.
    // You can initialize other member using a designated initializer.
    if (equal(tok, "{") && equal(tok->next, "."))
    {
        Member *mem = struct_designator(&tok, tok->next, init->ty);
        init->mem = mem;
        designation(&tok, tok, init->children[mem->idx]);
        *rest = skip(tok, "}");
        return;
    }

    if (equal(tok, "{"))
    {
        initializer2(&tok, tok->next, init->children[0]);
        consume(&tok, tok, ",");
        *rest = skip(tok, "}");
    }
    else
    {
        initializer2(rest, tok, init->children[0]);
    }
}

void initializer2(Token **rest, Token *tok, Initializer *init)
{
    if (init->ty->kind == TY_ARRAY && tok->kind == TK_STR)
    {
        string_initializer(rest, tok, init);
        return;
    }

    if (init->ty->kind == TY_ARRAY)
    {
        if (equal(tok, "{"))
        {
            array_initializer1(rest, tok, init);
        }
        else
        {
            array_initializer2(rest, tok, init, 0);
        }
        return;
    }

    if (init->ty->kind == TY_STRUCT)
    {
        if (equal(tok, "{"))
        {
            struct_initializer1(rest, tok, init);
            return;
        }

        // A struct can be initialized with another struct. E.g.
        // `struct T x = y;` where y is a variable of type `struct T`.
        // Handle that case first.

        Node *expr = assign(rest, tok);
        add_type(expr);
        if (expr->ty->kind == TY_STRUCT)
        {
            init->expr = expr;
            return;
        }
        struct_initializer2(rest, tok, init, init->ty->members);
        return;
    }

    if (init->ty->kind == TY_UNION)
    {
        union_initializer(rest, tok, init);
        return;
    }

    if (equal(tok, "{"))
    {
        // An initializer for a scalar variable can be surrounded by
        // braces. E.g. `int x = {3};`. Handle that case.
        initializer2(&tok, tok->next, init);
        *rest = skip(tok, "}");
        return;
    }

    init->expr = assign(&tok, tok);
    *rest = tok;
    return;
}

static Type *copy_struct_type(Type *ty)
{
    ty = copy_type(ty);

    Member head = {};
    Member *cur = &head;
    for (Member *mem = ty->members; mem; mem = mem->next)
    {
        Member *m = calloc(1, sizeof(Member));
        *m = *mem;
        cur = cur->next = m;
    }

    ty->members = head.next;
    return ty;
}

// initializer = "{" initializer ("," initializer)* "}"
//              | assign
static Initializer *initializer(Token **rest, Token *tok, Obj *var)
{
    Initializer *init = new_initializer(var->ty, var, true);
    initializer2(&tok, tok, init);

    if ((var->ty->kind == TY_STRUCT || var->ty->kind == TY_UNION) && var->ty->is_flexible)
    {
        Type *ty = copy_struct_type(var->ty);
        Member *mem = ty->members;
        while (mem->next)
        {
            mem = mem->next;
        }
        mem->ty = init->children[mem->idx]->ty;
        ty->size += mem->ty->size;
        var->ty = ty;
    }
    *rest = tok;
    return init;
}

static Node *init_desg_expr(Initializer *init, Token *tok)
{
    if (init->var)
    {
        return new_var_node(init->var, tok);
    }
    if (init->mem)
    {
        Node *node = new_unary(ND_MEMBER, init_desg_expr(init->next, tok), tok);
        node->member = init->mem;
        return node;
    }
    Node *lhs = init_desg_expr(init->next, tok);
    Node *rhs = new_num(init->idx, tok);
    return new_unary(ND_DEREF, new_add(lhs, rhs, tok), tok);
}

static Node *create_lvar_init(Initializer *init, Token *tok)
{
    if (init->ty->kind == TY_ARRAY)
    {
        Node *node = new_node(ND_NULL_EXPR, tok);
        for (int i = 0; i < init->ty->array_len; i++)
        {
            Node *rhs = create_lvar_init(init->children[i], tok);
            node = new_binary(ND_COMMA, node, rhs, tok);
        }
        return node;
    }

    if (init->ty->kind == TY_STRUCT && !init->expr)
    {
        Node *node = new_node(ND_NULL_EXPR, tok);
        for (Member *mem = init->ty->members; mem; mem = mem->next)
        {
            Node *rhs = create_lvar_init(init->children[mem->idx], tok);
            node = new_binary(ND_COMMA, node, rhs, tok);
        }
        return node;
    }

    if (init->ty->kind == TY_UNION)
    {
        Member *mem = init->mem ? init->mem : init->ty->members;
        return create_lvar_init(init->children[mem->idx], tok);
    }

    if (!init->expr)
    {
        return new_node(ND_NULL_EXPR, tok);
    }

    Node *lhs = init_desg_expr(init, tok);
    return new_binary(ND_ASSIGN, lhs, init->expr, tok);
}

// A variable definition with an initializer is a shorthand notation
// for a variable definition followed by assignments. This function
// generates assignment expressions for an initializer. For example,
// `int x[2][2] = {{6, 7}, {8, 9}}` is converted to the following
// expressions:
//
//   x[0][0] = 6;
//   x[0][1] = 7;
//   x[1][0] = 8;
//   x[1][1] = 9;
static Node *lvar_initializer(Token **rest, Token *tok, Obj *var)
{
    Initializer *init = initializer(&tok, tok, var);

    // If a partial initializer list is given, the standard requires
    // that unspecified elements are set to 0. Here, we simply
    // zero-initialize the entire memory region of a variable before
    // initializing it with user-supplied values.
    Node *lhs = new_node(ND_MEMZERO, tok);
    lhs->var = var;

    *rest = tok;
    return new_binary(ND_COMMA, lhs, create_lvar_init(init, tok), tok);
}

// declaration = (declarator ("=" assign)? (",", declarator ("=" assign)?)*)? ";"
static Node *declaration(Token **rest, Token *tok, Type *basety, VarAttr *attr)
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
        if (!ty->name)
        {
            error_tok(ty->name_pos, "variable name omitted");
        }

        // static local variable
        if (attr && attr->is_static)
        {
            Obj *var = new_anon_gvar(ty);
            if (attr && attr->align)
            {
                var->align = attr->align;
            }
            push_scope(get_ident(ty->name))->var = var;
            if (equal(tok, "="))
            {
                gvar_initializer(&tok, tok->next, var);
            }
            continue;
        }

        Obj *var = new_lvar(get_ident(ty->name), ty);
        if (attr && attr->align)
        {
            var->align = attr->align;
        }

        if (!equal(tok, "="))
        {
            continue;
        }
        Node *node = lvar_initializer(&tok, tok->next, var);
        if (var->ty->size < 0)
        {
            error_tok(ty->name, "variable has incomplete type");
        }
        if (var->ty->kind == TY_VOID)
        {
            error_tok(ty->name, "variable declared void");
        }
        cur = cur->next = new_unary(ND_EXPR_STMT, node, tok);
    }
    Node *node = new_node(ND_BLOCK, tok);
    node->body = head.next;
    *rest = tok->next;
    return node;
}

// asm-stmt = "asm" ("volatile" | "inline")* "(" string-literal ")"
static Node *asm_stmt(Token **rest, Token *tok)
{
    Node *node = new_node(ND_ASM, tok);
    tok = tok->next;

    while (equal(tok, "volatile") || equal(tok, "inline"))
    {
        tok = tok->next;
    }

    tok = skip(tok, "(");
    if (tok->kind != TK_STR || tok->ty->base->kind != TY_CHAR)
    {
        error_tok(tok, "expected string literal");
    }
    node->asm_str = tok->str;
    *rest = skip(tok->next, ")");
    return node;
}

// stmt = "return" expr? ";"
//      | expr-stmt
//      | "{" compound-stmt
//      | "if" "(" expr ")" stmt ("else" stmt)?
//      | "switch" "(" expr ")" stmt
//      | "case" num ":" stmt
//      | "default" ":" stmt
//      | "for" "(" expr-stmt expr? ";" expr? ")" stmt
//      | "while" "(" expr ")" stmt
//      | "do" stmt "while" "(" expr ")" ";"
//      | goto ident ";"
//      | break ";"
//      | ident ":" stmt
//      | "asm" asm-stmt
static Node *stmt(Token **rest, Token *tok)
{
    if (equal(tok, "switch"))
    {
        Node *node = new_node(ND_SWITCH, tok);
        tok = skip(tok->next, "(");
        node->cond = expr(&tok, tok);
        tok = skip(tok, ")");

        Node *sw = current_switch;
        current_switch = node;

        char *brk = brk_label;
        brk_label = node->brk_label = new_unique_name();
        node->then = stmt(&tok, tok);
        current_switch = sw;
        brk_label = brk;

        *rest = tok;
        return node;
    }

    if (equal(tok, "case"))
    {
        if (!current_switch)
        {
            error_tok(tok, "stray case");
        }
        Node *node = new_node(ND_CASE, tok);
        tok = tok->next;
        long val = const_expr(&tok, tok);
        tok = skip(tok, ":");
        node->label = new_unique_name();
        node->lhs = stmt(&tok, tok);
        node->val = val;
        node->case_next = current_switch->case_next;
        current_switch->case_next = node;

        *rest = tok;
        return node;
    }

    if (equal(tok, "default"))
    {
        if (!current_switch)
        {
            error_tok(tok, "stray default");
        }
        Node *node = new_node(ND_CASE, tok);
        tok = skip(tok->next, ":");
        node->label = new_unique_name();
        node->lhs = stmt(rest, tok);
        current_switch->default_case = node;
        return node;
    }

    if (equal(tok, "break"))
    {
        if (!brk_label)
        {
            error_tok(tok, "stray break");
        }
        Node *node = new_node(ND_GOTO, tok);
        node->unique_label = brk_label;
        *rest = skip(tok->next, ";");
        return node;
    }

    if (equal(tok, "continue"))
    {
        if (!cont_label)
        {
            error_tok(tok, "stray continue");
        }
        Node *node = new_node(ND_GOTO, tok);
        node->unique_label = cont_label;
        *rest = skip(tok->next, ";");
        return node;
    }

    if (equal(tok, "goto"))
    {
        Node *node = new_node(ND_GOTO, tok);
        tok = tok->next;
        node->label = get_ident(tok);
        tok = skip(tok->next, ";");
        node->goto_next = gotos;
        gotos = node;
        *rest = tok;
        return node;
    }

    if (tok->kind == TK_IDENT && equal(tok->next, ":"))
    {
        Node *node = new_node(ND_LABEL, tok);
        node->label = get_ident(tok);
        node->unique_label = new_unique_name();
        node->goto_next = labels;
        labels = node;
        node->lhs = stmt(&tok, tok->next->next);
        *rest = tok;
        return node;
    }

    if (equal(tok, "while"))
    {
        tok = skip(tok->next, "(");
        Node *node = new_node(ND_FOR, tok);
        node->cond = expr(&tok, tok);
        tok = skip(tok, ")");

        char *brk = brk_label;
        char *cont = cont_label;
        brk_label = node->brk_label = new_unique_name();
        cont_label = node->cont_label = new_unique_name();
        node->then = stmt(&tok, tok);
        brk_label = brk;
        cont_label = cont;
        *rest = tok;
        return node;
    }

    if (equal(tok, "do"))
    {
        Node *node = new_node(ND_DO, tok);

        char *brk = brk_label;
        char *cont = cont_label;
        brk_label = node->brk_label = new_unique_name();
        cont_label = node->cont_label = new_unique_name();

        node->then = stmt(&tok, tok->next);

        brk_label = brk;
        cont_label = cont;

        tok = skip(tok, "while");
        tok = skip(tok, "(");
        node->cond = expr(&tok, tok);
        tok = skip(tok, ")");
        *rest = skip(tok, ";");
        return node;
    }

    if (equal(tok, "for"))
    {
        Node *node = new_node(ND_FOR, tok);
        tok = skip(tok->next, "(");
        enter_scope();

        char *brk = brk_label;
        char *cont = cont_label;
        brk_label = node->brk_label = new_unique_name();
        cont_label = node->cont_label = new_unique_name();

        if (is_typename(tok))
        {
            Type *basety = declspec(&tok, tok, NULL);
            node->init = declaration(&tok, tok, basety, NULL);
        }
        else
        {
            node->init = expr_stmt(&tok, tok);
        }
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
        leave_scope();
        brk_label = brk;
        cont_label = cont;
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
        if (consume(rest, tok->next, ";"))
        {
            return node;
        }
        Node *exp = expr(&tok, tok->next);
        tok = skip(tok, ";");
        add_type(exp);

        Type *ty = current_fn->ty->return_ty;
        if (ty->kind != TY_STRUCT && ty->kind != TY_UNION)
        {
            exp = new_cast(exp, current_fn->ty->return_ty);
        }

        node->lhs = exp;
        *rest = tok;
        return node;
    }

    if (equal(tok, "{"))
    {
        Node *node = compound_stmt(&tok, tok->next);
        *rest = tok;
        return node;
    }

    if (equal(tok, "asm"))
    {
        return asm_stmt(rest, tok);
    }
    return expr_stmt(rest, tok);
}

static bool is_typename(Token *tok)
{
    static char *kw[] = {"void", "char", "short", "int",
                         "long", "struct", "union", "typedef",
                         "_Bool", "enum", "static", "extern",
                         "_Alignas", "signed", "unsigned", "const",
                         "volatile", "auto", "register", "restrict",
                         "__restrict", "__restrict__", "_Noreturn",
                         "float", "double", "typeof", "inline"};

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
static Node *compound_stmt(Token **rest, Token *tok)
{
    Node *node = new_node(ND_BLOCK, tok);
    Node head = {};
    Node *cur = &head;
    enter_scope();
    while (!equal(tok, "}"))
    {
        if (is_typename(tok) && !equal(tok->next, ":"))
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
                tok = function(tok, basety, &attr);
                continue;
            }

            if (attr.is_extern)
            {
                tok = global_variable(tok, basety, &attr);
                continue;
            }

            cur = cur->next = declaration(&tok, tok, basety, &attr);
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
        if (!param->name)
        {
            error_tok(param->name_pos, "parameter name omitted");
        }
        new_lvar(get_ident(param->name), param);
    }
}

// This function matches gotos with labels.
//
// We cannot resolve gotos as we parse a function because gotos
// can refer a label that appears later in the function.
// So, we need to do this after we parse the entire function.
static void resolve_goto_labels(void)
{
    for (Node *x = gotos; x; x = x->goto_next)
    {
        for (Node *y = labels; y; y = y->goto_next)
        {
            if (!strcmp(x->label, y->label))
            {
                x->unique_label = y->unique_label;
                break;
            }
        }
        if (x->unique_label == NULL)
        {
            error_tok(x->tok->next, "use of undeclared label");
        }
    }
    gotos = labels = NULL;
}

// function = declspec declarator "{" compound_stmt
static Token *function(Token *tok, Type *basety, VarAttr *attr)
{
    Type *ty = declarator(&tok, tok, basety);
    if (!ty->name)
    {
        error_tok(ty->name_pos, "function name omitted");
    }

    Obj *fn = new_gvar(get_ident(ty->name), ty);
    fn->is_function = true;
    fn->is_definition = !consume(&tok, tok, ";");
    fn->is_static = attr->is_static || (attr->is_inline && !attr->is_extern);
    if (!fn->is_definition)
    {
        return tok;
    }

    current_fn = fn;
    locals = NULL;
    enter_scope();
    create_param_lvars(ty->params);

    // A buffer for a struct/union return value is passed
    // as the hidden first parameter.
    Type *rty = ty->return_ty;
    if ((rty->kind == TY_STRUCT || rty->kind == TY_UNION) && rty->size > 16)
    {
        new_lvar("", pointer_to(rty));
    }

    fn->params = locals;
    if (ty->is_variadic)
    {
        fn->va_area = new_lvar("__va_area__", array_of(ty_char, 136));
    }

    tok = skip(tok, "{");
    push_scope("__func__")->var =
        new_string_literal(fn->name, array_of(ty_char, strlen(fn->name) + 1));
    // [GNU] __FUNCTION__ is yet another name of __func__.
    push_scope("__FUNCTION__")->var =
        new_string_literal(fn->name, array_of(ty_char, strlen(fn->name) + 1));

    fn->body = compound_stmt(&tok, tok);
    fn->locals = locals;
    leave_scope();
    resolve_goto_labels();
    return tok;
}

static bool is_function(Token *tok)
{
    if (equal(tok, ";"))
    {
        return false;
    }

    Type dummy = {};
    Type *ty = declarator(&tok, tok, &dummy);
    if (!ty->name)
    {
        return false;
    }
    return ty->kind == TY_FUNC;
}

static void write_buf(char *buf, uint64_t val, int sz)
{
    if (sz == 1)
    {
        *buf = val;
    }
    else if (sz == 2)
    {
        *(uint16_t *)buf = val;
    }
    else if (sz == 4)
    {
        *(uint32_t *)buf = val;
    }
    else if (sz == 8)
    {
        *(uint64_t *)buf = val;
    }
    else
    {
        unreachable();
    }
}

static uint64_t read_buf(char *buf, int sz)
{
    if (sz == 1)
    {
        return *buf;
    }
    if (sz == 2)
    {
        return *(uint16_t *)buf;
    }
    if (sz == 4)
    {
        return *(uint32_t *)buf;
    }
    if (sz == 8)
    {
        return *(uint64_t *)buf;
    }
    unreachable();
}

static Relocation *write_gvar_data(Relocation *cur, Initializer *init, char *buf, int offset)
{
    if (init->ty->kind == TY_ARRAY)
    {
        int sz = init->ty->base->size;
        for (int i = 0; i < init->ty->array_len; i++)
        {
            cur = write_gvar_data(cur, init->children[i], buf, offset + sz * i);
        }
        return cur;
    }

    if (init->ty->kind == TY_STRUCT)
    {
        for (Member *mem = init->ty->members; mem; mem = mem->next)
        {
            if (mem->is_bitfield)
            {
                Node *expr = init->children[mem->idx]->expr;
                if (!expr)
                {
                    break;
                }

                char *loc = buf + offset + mem->offset;
                uint64_t oldval = read_buf(loc, mem->ty->size);
                uint64_t newval = eval(expr);
                uint64_t mask = (1L << mem->bit_width) - 1;
                uint64_t combined = oldval | ((newval & mask) << mem->bit_offset);
                write_buf(loc, combined, mem->ty->size);
            }
            else
            {
                cur = write_gvar_data(cur, init->children[mem->idx], buf, offset + mem->offset);
            }
        }
        return cur;
    }

    if (init->ty->kind == TY_UNION)
    {
        Member *mem = init->mem ? init->mem : init->ty->members;
        cur = write_gvar_data(cur, init->children[mem->idx], buf, offset);
        return cur;
    }

    if (!init->expr)
    {
        return cur;
    }

    if (init->ty->kind == TY_FLOAT)
    {
        *(float *)(buf + offset) = eval_double(init->expr);
        return cur;
    }

    if (init->ty->kind == TY_DOUBLE)
    {
        *(double *)(buf + offset) = eval_double(init->expr);
        return cur;
    }

    char *label = NULL;
    uint64_t val = eval2(init->expr, &label);

    if (!label)
    {
        write_buf(buf + offset, val, init->ty->size);
        return cur;
    }

    Relocation *rel = calloc(1, sizeof(Relocation));
    rel->offset = offset;
    rel->label = label;
    rel->addend = val;
    cur->next = rel;
    return cur->next;
}

static void gvar_initializer(Token **rest, Token *tok, Obj *var)
{
    Initializer *init = initializer(rest, tok, var);
    Relocation head = {};
    char *buf = calloc(1, var->ty->size);
    write_gvar_data(&head, init, buf, 0);
    var->init_data = buf;
    var->rel = head.next;
}

static Token *global_variable(Token *tok, Type *basety, VarAttr *attr)
{
    int i = 0;
    while (!equal(tok, ";"))
    {
        if (i++ > 0)
        {
            tok = skip(tok, ",");
        }
        Type *ty = declarator(&tok, tok, basety);
        if (!ty->name)
        {
            error_tok(ty->name_pos, "variable name omitted");
        }

        Obj *var = new_gvar(get_ident(ty->name), ty);
        var->is_definition = !attr->is_extern;
        var->is_static = attr->is_static;
        if (attr->align)
        {
            var->align = attr->align;
        }
        if (equal(tok, "="))
        {
            gvar_initializer(&tok, tok->next, var);
        }
    }
    tok = skip(tok, ";");
    return tok;
}

// typedef = (declarator ("," declarator)*)*
static Token *parse_typedef(Token *tok, Type *basety)
{
    int i = 0;
    while (!consume(&tok, tok, ";"))
    {
        if (i++ > 0)
        {
            tok = skip(tok, ",");
        }
        Type *ty = declarator(&tok, tok, basety);
        if (!ty->name)
        {
            error_tok(ty->name_pos, "typedef name omitted");
        }
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
            tok = function(tok, basety, &attr);
            continue;
        }

        tok = global_variable(tok, basety, &attr);
    }
    return globals;
}