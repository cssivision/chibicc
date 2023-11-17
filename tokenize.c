#include "chibicc.h"

static File *current_file;
static File **input_files;

// True if the current position is at the beginning of a line
static bool at_bol;
static bool has_space;

// Reports an error message in the following format and exit.
//
// foo.c:10: x = y + 1;
//               ^ <error message here>
void verror_at(char *filename, char *input, int line_no, char *loc, char *fmt, va_list ap)
{
    char *line = loc;
    while (line > input && line[-1] != '\n')
    {
        line--;
    }
    char *end = loc;
    while (*end && *end != '\n')
    {
        end++;
    }
    int indent = fprintf(stderr, "%s:%d: ", filename, line_no);
    fprintf(stderr, "%.*s\n", (int)(end - line), line);

    // Show the error message.
    int pos = loc - line + indent;

    fprintf(stderr, "%*s", pos, ""); // print pos spaces.
    fprintf(stderr, "^ ");
    vfprintf(stderr, fmt, ap);
    fprintf(stderr, "\n");
}

void warn_tok(Token *tok, char *fmt, ...)
{
    va_list ap;
    va_start(ap, fmt);
    verror_at(tok->file->name, tok->file->contents, tok->line_no, tok->loc, fmt, ap);
    va_end(ap);
}

void error_at(char *loc, char *fmt, ...)
{
    int line_no = 1;
    for (char *p = current_file->contents; p < loc; p++)
    {
        if (*p == '\n')
        {
            line_no++;
        }
    }
    va_list ap;
    va_start(ap, fmt);
    verror_at(current_file->name, current_file->contents, line_no, loc, fmt, ap);
    exit(1);
}

void error_tok(Token *tok, char *fmt, ...)
{
    va_list ap;
    va_start(ap, fmt);
    verror_at(tok->file->name, tok->file->contents, tok->line_no, tok->loc, fmt, ap);
    exit(1);
}

Token *new_token(TokenKind kind, char *start, char *end)
{
    Token *tok = calloc(1, sizeof(Token));
    tok->kind = kind;
    tok->loc = start;
    tok->len = end - start;
    tok->at_bol = at_bol;
    tok->file = current_file;
    tok->has_space = has_space;
    at_bol = has_space = false;
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
        "==", "!=", "<=", ">=", "->", "+=", "-=", "*=", "/=", "++",
        "--", "%=", "|=", "&=", "^=", "||", "&&", "<<=", ">>=", "<<",
        ">>", "...", "##"};
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
                         "long", "void", "typedef", "_Bool", "enum",
                         "static", "goto", "break", "continue",
                         "switch", "case", "default", "extern",
                         "_Alignof", "_Alignas", "do", "signed",
                         "const", "volatile", "auto", "register",
                         "restrict", "__restrict", "__restrict__",
                         "_Noreturn", "float", "double"};
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
    char *p = current_file->contents;
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
    tok->ty = ty_int;
    return tok;
}

static Token *read_int_literal(char *start)
{
    char *p = start;
    int base = 10;
    if (!strncasecmp(p, "0x", 2) && isxdigit(p[2]))
    {
        p += 2;
        base = 16;
    }
    else if (!strncasecmp(p, "0b", 2) && (p[2] == '0' || p[2] == '1'))
    {
        p += 2;
        base = 2;
    }
    else if (*p == '0')
    {
        base = 8;
    }

    int64_t val = strtoul(p, &p, base);

    // Read U, L or LL suffixes.
    bool l = false;
    bool u = false;

    if (startswith(p, "LLU") || startswith(p, "LLu") ||
        startswith(p, "llU") || startswith(p, "llu") ||
        startswith(p, "ULL") || startswith(p, "Ull") ||
        startswith(p, "uLL") || startswith(p, "ull"))
    {
        p += 3;
        l = u = true;
    }
    else if (!strncasecmp(p, "lu", 2) || !strncasecmp(p, "ul", 2))
    {
        p += 2;
        l = u = true;
    }
    else if (startswith(p, "LL") || startswith(p, "ll"))
    {
        p += 2;
        l = true;
    }
    else if (*p == 'L' || *p == 'l')
    {
        p++;
        l = true;
    }
    else if (*p == 'U' || *p == 'u')
    {
        p++;
        u = true;
    }

    // Infer a type.
    Type *ty;
    if (base == 10)
    {
        if (l && u)
        {
            ty = ty_ulong;
        }
        else if (l)
        {
            ty = ty_long;
        }
        else if (u)
        {
            ty = (val >> 32) ? ty_ulong : ty_uint;
        }
        else
        {
            ty = (val >> 31) ? ty_long : ty_int;
        }
    }
    else
    {
        if (l && u)
        {
            ty = ty_ulong;
        }
        else if (l)
        {
            ty = (val >> 63) ? ty_ulong : ty_long;
        }
        else if (u)
        {
            ty = (val >> 32) ? ty_ulong : ty_uint;
        }
        else if (val >> 63)
        {
            ty = ty_ulong;
        }
        else if (val >> 32)
        {
            ty = ty_long;
        }
        else if (val >> 31)
        {
            ty = ty_uint;
        }
        else
        {
            ty = ty_int;
        }
    }

    Token *tok = new_token(TK_NUM, start, p);
    tok->val = val;
    tok->ty = ty;
    return tok;
}

static Token *read_number(char *start)
{
    // Try to parse as an integer constant.
    Token *tok = read_int_literal(start);
    if (!strchr(".eEfF", start[tok->len]))
    {
        return tok;
    }

    // If it's not an integer, it must be a floating point constant.
    char *end;
    double val = strtod(start, &end);

    Type *ty;
    if (*end == 'f' || *end == 'F')
    {
        ty = ty_float;
        end++;
    }
    else if (*end == 'l' || *end == 'L')
    {
        ty = ty_double;
        end++;
    }
    else
    {
        ty = ty_double;
    }

    tok = new_token(TK_NUM, start, end);
    tok->fval = val;
    tok->ty = ty;
    return tok;
}

Token *tokenize(File *file)
{
    current_file = file;
    char *p = current_file->contents;

    Token head = {};
    Token *cur = &head;

    at_bol = true;
    has_space = false;

    while (*p)
    {
        // Skip line comments.
        if (startswith(p, "//"))
        {
            p += 2;
            while (*p != '\n')
            {
                p++;
            }
            has_space = true;
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
            has_space = true;
            continue;
        }

        // Skip newline.
        if (*p == '\n')
        {
            p++;
            at_bol = true;
            has_space = true;
            continue;
        }

        if (isspace(*p))
        {
            p++;
            has_space = true;
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

        if (isdigit(*p) || (*p == '.' && isdigit(p[1])))
        {
            cur = cur->next = read_number(p);
            p += cur->len;
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
            return NULL;
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

File *new_file(char *name, int file_no, char *contents)
{
    File *file = calloc(1, sizeof(File));
    file->name = name;
    file->file_no = file_no;
    file->contents = contents;
    return file;
}

File **get_input_files(void)
{
    return input_files;
}

Token *tokenize_file(char *path)
{
    char *p = read_file(path);
    if (!p)
    {
        return NULL;
    }

    static int file_no;
    File *file = new_file(path, file_no + 1, p);

    // Save the filename for assembler .file directive.
    input_files = realloc(input_files, sizeof(char *) * (file_no + 2));
    input_files[file_no] = file;
    input_files[file_no + 1] = NULL;
    file_no++;

    return tokenize(file);
}