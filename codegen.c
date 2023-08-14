#include "chibicc.h"

static int depth;

void push(void)
{
    printf("  push %%rax\n");
    depth++;
}

void pop(char *arg)
{
    printf("  pop %s\n", arg);
    depth--;
}

void gen_expr(Node *node)
{
    if (node->kind == ND_NUM)
    {
        printf("  mov $%d, %%rax\n", node->val);
        return;
    }

    if (node->rhs)
    {
        gen_expr(node->rhs);
        push();
    }
    if (node->lhs)
    {
        gen_expr(node->lhs);
    }
    if (node->rhs)
    {
        pop("%rdi");
    }

    switch (node->kind)
    {
    case ND_NEG:
        printf("  neg %%rax\n");
        return;
    case ND_ADD:
        printf("  add %%rdi, %%rax\n");
        return;
    case ND_SUB:
        printf("  sub %%rdi, %%rax\n");
        return;
    case ND_MUL:
        printf("  imul %%rdi, %%rax\n");
        return;
    case ND_DIV:
        printf("  cqo\n");
        printf("  idiv %%rdi\n");
        return;
    case ND_EQ:
    case ND_NE:
    case ND_LT:
    case ND_LE:
        printf("  cmp %%rdi, %%rax\n");

        if (node->kind == ND_EQ)
            printf("  sete %%al\n");
        else if (node->kind == ND_NE)
            printf("  setne %%al\n");
        else if (node->kind == ND_LT)
            printf("  setl %%al\n");
        else if (node->kind == ND_LE)
            printf("  setle %%al\n");

        printf("  movzb %%al, %%rax\n");
        return;
    }

    error("invalid expression");
}

static void gen_stmt(Node *node)
{
    if (node->kind == ND_EXPR_STMT)
    {
        gen_expr(node->lhs);
        return;
    }

    error("invalid statement");
}

void codegen(Node *node)
{
    printf("  .globl main\n");
    printf("main:\n");

    for (Node *n = node; n; n = n->next)
    {
        gen_stmt(n);
        assert(depth == 0);
    }

    printf("  ret\n");
}