#include "chibicc.h"

static char *current_input;
static char *current_filename;

// Reports an error message in the following format and exit.
//
// foo.c:10: x = y + 1;
//               ^ <error message here>
void verror_at(int line_no, char *loc, char *fmt, va_list ap)
{
    char *line = loc;
    while (line > current_input && line[-1] != '\n')
    {
        line--;
    }
    char *end = loc;
    while (*end != '\n')
    {
        end++;
    }
    int indent = fprintf(stderr, "%s:%d: ", current_filename, line_no);
    fprintf(stderr, "%.*s\n", (int)(end - line), line);

    // Show the error message.
    int pos = loc - line + indent;

    fprintf(stderr, "%*s", pos, ""); // print pos spaces.
    fprintf(stderr, "^ ");
    vfprintf(stderr, fmt, ap);
    fprintf(stderr, "\n");
}

void error_at(char *loc, char *fmt, ...)
{
    int line_no = 1;
    for (char *p = current_input; p < loc; p++)
    {
        if (*p == '\n')
        {
            line_no++;
        }
    }
    va_list ap;
    va_start(ap, fmt);
    verror_at(line_no, loc, fmt, ap);
    exit(1);
}

void error_tok(Token *tok, char *fmt, ...)
{
    va_list ap;
    va_start(ap, fmt);
    verror_at(tok->line_no, tok->loc, fmt, ap);
    exit(1);
}

Token *new_token(TokenKind kind, char *start, char *end)
{
    Token *tok = calloc(1, sizeof(Token));
    tok->kind = kind;
    tok->loc = start;
    tok->len = end - start;
    return tok;
}

bool consume(Token **rest, Token *tok, char *str)
{
    if (equal(tok, str))
    {
        *rest = tok->next;
        return true;
    }
    *rest = tok;
    return false;
}

bool startswith(char *p, char *q)
{
    return strncmp(p, q, strlen(q)) == 0;
}

int read_punct(char *p)
{
    static char *kw[] = {
        "==",
        "!=",
        "<=",
        ">=",
        "->",
        "+=",
        "-=",
        "*=",
        "/=",
        "++",
        "--",
    };
    for (int i = 0; i < sizeof(kw) / sizeof(*kw); i++)
    {
        if (startswith(p, kw[i]))
        {
            return strlen(kw[i]);
        }
    }
    return ispunct(*p) ? 1 : 0;
}

bool is_ident1(char c)
{
    return ('a' <= c && c <= 'z') || ('A' <= c && c <= 'Z') || c == '_';
}

bool is_ident2(char c)
{
    return is_ident1(c) || ('0' <= c && c <= '9');
}

bool is_keywords(Token *tok)
{
    static char *kw[] = {"return", "if", "else", "while", "int",
                         "sizeof", "char", "struct", "union", "short",
                         "long", "void", "typedef", "_Bool", "enum", "static"};
    for (int i = 0; i < sizeof(kw) / sizeof(*kw); i++)
    {
        if (equal(tok, kw[i]))
        {
            return true;
        }
    }
    return false;
}

void convert_keywords(Token *tok)
{
    for (Token *t = tok; t->kind != TK_EOF; t = t->next)
    {
        if (is_keywords(t))
        {
            t->kind = TK_KEYWORD;
        }
    }
}

char *string_literal_end(char *p)
{
    char *start = p;
    for (; *p != '"'; p++)
    {
        if (*p == '\n' || *p == '\0')
        {
            error_at(start, "unclosed string literal");
        }
        if (*p == '\\')
        {
            p++;
        }
    }
    return p;
}

int from_hex(char c)
{
    if ('0' <= c && c <= '9')
    {
        return c - '0';
    }
    if ('a' <= c && c <= 'f')
    {
        return c - 'a' + 10;
    }
    return c - 'A' + 10;
}

int read_escaped_char(char **new_pos, char *p)
{
    if ('0' <= *p && *p <= '7')
    {
        int c = *p++ - '0';
        if ('0' <= *p && *p <= '7')
        {
            c = (c << 3) + (*p++ - '0');
            if ('0' <= *p && *p <= '7')
            {
                c = (c << 3) + (*p++ - '0');
            }
        }
        *new_pos = p;

        return c;
    }

    if (*p == 'x')
    {
        p++;
        if (!isxdigit(*p))
        {
            error_at(p, "invalid hex escape sequence");
        }

        int c = 0;
        for (; isxdigit(*p); p++)
        {
            c = (c << 4) + from_hex(*p);
        }
        *new_pos = p;
        return c;
    }

    *new_pos = p + 1;
    // Escape sequences are defined using themselves here. E.g.
    // '\n' is implemented using '\n'. This tautological definition
    // works because the compiler that compiles our compiler knows
    // what '\n' actually is. In other words, we "inherit" the ASCII
    // code of '\n' from the compiler that compiles our compiler,
    // so we don't have to teach the actual code here.
    //
    // This fact has huge implications not only for the correctness
    // of the compiler but also for the security of the generated code.
    // For more info, read "Reflections on Trusting Trust" by Ken Thompson.
    // https://github.com/rui314/chibicc/wiki/thompson1984.pdf
    switch (*p)
    {
    case 'a':
        return '\a';
    case 'b':
        return '\b';
    case 't':
        return '\t';
    case 'n':
        return '\n';
    case 'v':
        return '\v';
    case 'f':
        return '\f';
    case 'r':
        return '\r';
    // [GNU] \e for the ASCII escape character is a GNU C extension.
    case 'e':
        return 27;
    default:
        return *p;
    }
}

Token *read_string_literal(char *start)
{
    char *end = string_literal_end(start + 1);
    char *buf = calloc(1, end - start);

    int len = 0;
    for (char *p = start + 1; p < end;)
    {
        if (*p == '\\')
        {
            buf[len++] = read_escaped_char(&p, p + 1);
        }
        else
        {
            buf[len++] = *p++;
        }
    }
    Token *tok = new_token(TK_STR, start, end + 1);
    tok->ty = array_of(ty_char, len + 1);
    tok->str = buf;
    return tok;
}

// Initialize line info for all tokens.
static void add_line_numbers(Token *tok)
{
    char *p = current_input;
    int n = 1;

    do
    {
        if (p == tok->loc)
        {
            tok->line_no = n;
            tok = tok->next;
        }
        if (*p == '\n')
        {
            n++;
        }
    } while (*p++);
}

Token *read_char_literal(char *start)
{
    char *p = start + 1;
    if (*p == '\0')
    {
        error_at(start, "unclosed char literal");
    }

    char c;
    if (*p == '\\')
    {
        c = read_escaped_char(&p, p + 1);
    }
    else
    {
        c = *p++;
    }

    char *end = strchr(p, '\'');
    if (!end)
    {
        error_at(p, "unclosed char literal");
    }
    Token *tok = new_token(TK_NUM, start, end + 1);
    tok->val = c;
    return tok;
}

Token *tokenize(char *path, char *p)
{
    current_filename = path;
    current_input = p;

    Token head = {};
    Token *cur = &head;

    while (*p)
    {
        // Skip line comments.
        if (startswith(p, "//"))
        {
            p += 2;
            while (*p != '\n')
                p++;
            continue;
        }

        // Skip block comments.
        if (startswith(p, "/*"))
        {
            char *q = strstr(p + 2, "*/");
            if (!q)
            {
                error_at(p, "unclosed block comment");
            }
            p = q + 2;
            continue;
        }

        if (isspace(*p))
        {
            p++;
            continue;
        }

        if (*p == '"')
        {
            cur = cur->next = read_string_literal(p);
            p += cur->len;
            continue;
        }

        if (*p == '\'')
        {
            cur = cur->next = read_char_literal(p);
            p += cur->len;
            continue;
        }

        if (isdigit(*p))
        {
            cur = cur->next = new_token(TK_NUM, p, p);
            char *q = p;
            cur->val = strtoul(p, &p, 10);
            cur->len = p - q;
            continue;
        }

        // Identifier or keyword
        if (is_ident1(*p))
        {
            char *start = p;
            do
            {
                p++;
            } while (is_ident2(*p));
            cur = cur->next = new_token(TK_IDENT, start, p);
            continue;
        }

        int punct_len = read_punct(p);
        if (punct_len)
        {
            cur = cur->next = new_token(TK_PUNCT, p, p + punct_len);
            p += cur->len;
            continue;
        }

        error_at(p, "invalid token");
    }

    cur = cur->next = new_token(TK_EOF, p, p);
    convert_keywords(head.next);
    add_line_numbers(head.next);
    return head.next;
}

void error(char *fmt, ...)
{
    va_list ap;
    va_start(ap, fmt);
    vfprintf(stderr, fmt, ap);
    fprintf(stderr, "\n");
    exit(1);
}

char *read_file(char *path)
{
    FILE *fp;
    if (strcmp(path, "-") == 0)
    {
        fp = stdin;
    }
    else
    {
        fp = fopen(path, "r");
        if (!fp)
        {
            error("cannot open %s: %s", path, strerror(errno));
        }
    }

    char *buf;
    size_t buflen;
    FILE *out = open_memstream(&buf, &buflen);

    for (;;)
    {
        char *buf2[4096];
        int n = fread(buf2, 1, sizeof(buf2), fp);
        if (n == 0)
        {
            break;
        }
        fwrite(buf2, 1, n, out);
    }

    if (fp != stdin)
    {
        fclose(fp);
    }
    fflush(out);
    if (buflen == 0 || buf[buflen - 1] != '\n')
    {
        fputc('\n', out);
    }
    fputc('\0', out);
    fclose(out);
    return buf;
}

Token *tokenize_file(char *path)
{
    return tokenize(path, read_file(path));
}