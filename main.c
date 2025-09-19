#include "mpc.h"

#ifdef _WIN32

static char buffer[2048];

char* readline(char* prompt) {
  fputs(prompt, stdout);
  fgets(buffer, 2048, stdin);
  char* cpy = malloc(strlen(buffer)+1);
  strcpy(cpy, buffer);
  cpy[strlen(cpy)-1] = '\0';
  return cpy;
}

void add_history(char* unused) {}

#else
#include <editline/readline.h>
#include <editline/history.h>
#endif
#include "spooky_hash.h" // Include file for the hash function

/* Parser Declarations */

mpc_parser_t* Number;
mpc_parser_t* Symbol;
mpc_parser_t* String;
mpc_parser_t* Comment;
mpc_parser_t* Sexpr;
mpc_parser_t* Qexpr;
mpc_parser_t* Expr;
mpc_parser_t* Lispy;

/* Forward Declarations */

struct lval;
struct lenv;
typedef struct lval lval;
typedef struct lenv lenv;

/* Lisp Value */

/* A enum with all the type of values */
enum { LVAL_ERR, LVAL_NUM,   LVAL_SYM, LVAL_STR,
       LVAL_FUN, LVAL_SEXPR, LVAL_QEXPR };

typedef lval*(*lbuiltin)(lenv*, lval*);

/* Main struct of the language */
struct lval {
  int type;

  /* Basic */
  long num;
  char* err;
  char* sym;
  char* str;

  /* Function */
  lbuiltin builtin;
  lenv* env;
  lval* formals;
  lval* body;

  /* Expression */
  int count;
  lval** cell;
};

/* struct used for a value in hash table */
struct HashEntry;
/* The struct used for set the values */
struct HashTable;

/* Lisp value constructors */
lval* lval_num(long x) {
  lval* v = malloc(sizeof(lval));
  v->type = LVAL_NUM;
  v->num = x;
  return v;
}

lval* lval_err(char* fmt, ...) {
  lval* v = malloc(sizeof(lval));
  v->type = LVAL_ERR;
  va_list va;
  va_start(va, fmt);
  v->err = malloc(512);
  vsnprintf(v->err, 511, fmt, va);
  v->err = realloc(v->err, strlen(v->err)+1);
  va_end(va);
  return v;
}

lval* lval_sym(char* s) {
  lval* v = malloc(sizeof(lval));
  v->type = LVAL_SYM;
  v->sym = malloc(strlen(s) + 1);
  strcpy(v->sym, s);
  return v;
}

lval* lval_str(char* s) {
  lval* v = malloc(sizeof(lval));
  v->type = LVAL_STR;
  v->str = malloc(strlen(s) + 1);
  strcpy(v->str, s);
  return v;
}

lval* lval_builtin(lbuiltin func) {
  lval* v = malloc(sizeof(lval));
  v->type = LVAL_FUN;
  v->builtin = func;
  return v;
}

lenv* lenv_new(void);

lval* lval_lambda(lval* formals, lval* body) {
  lval* v = malloc(sizeof(lval));
  v->type = LVAL_FUN;
  v->builtin = NULL;
  v->env = lenv_new();
  v->formals = formals;
  v->body = body;
  return v;
}

lval* lval_sexpr(void) {
  lval* v = malloc(sizeof(lval));
  v->type = LVAL_SEXPR;
  v->count = 0;
  v->cell = NULL;
  return v;
}

lval* lval_qexpr(void) {
  lval* v = malloc(sizeof(lval));
  v->type = LVAL_QEXPR;
  v->count = 0;
  v->cell = NULL;
  return v;
}

void lenv_del(lenv* e);

void lval_del(lval* v) {
  int i;
  switch (v->type) {
    case LVAL_NUM: break;
    case LVAL_FUN:
      if (!v->builtin) {
        lenv_del(v->env);
        lval_del(v->formals);
        lval_del(v->body);
      }
    break;
    case LVAL_ERR: free(v->err); break;
    case LVAL_SYM: free(v->sym); break;
    case LVAL_STR: free(v->str); break;
    case LVAL_QEXPR:
    case LVAL_SEXPR:
      for (i = 0; i < v->count; i++) {
        lval_del(v->cell[i]);
      }
      free(v->cell);
    break;
  }

  free(v);
}

lenv* lenv_copy(lenv* e);

lval* lval_copy(lval* v) {
  int i;
  lval* x = malloc(sizeof(lval));
  x->type = v->type;
  switch (v->type) {
    case LVAL_FUN:
      if (v->builtin) {
        x->builtin = v->builtin;
      } else {
        x->builtin = NULL;
        x->env = lenv_copy(v->env);
        x->formals = lval_copy(v->formals);
        x->body = lval_copy(v->body);
      }
    break;
    case LVAL_NUM: x->num = v->num; break;
    case LVAL_ERR: x->err = malloc(strlen(v->err) + 1);
      strcpy(x->err, v->err);
    break;
    case LVAL_SYM: x->sym = malloc(strlen(v->sym) + 1);
      strcpy(x->sym, v->sym);
    break;
    case LVAL_STR: x->str = malloc(strlen(v->str) + 1);
      strcpy(x->str, v->str);
    break;
    case LVAL_SEXPR:
    case LVAL_QEXPR:
      x->count = v->count;
      x->cell = malloc(sizeof(lval*) * x->count);
      for (i = 0; i < x->count; i++) {
        x->cell[i] = lval_copy(v->cell[i]);
      }
    break;
  }
  return x;
}

lval* lval_add(lval* v, lval* x) {
  v->count++;
  v->cell = realloc(v->cell, sizeof(lval*) * v->count);
  v->cell[v->count-1] = x;
  return v;
}

lval* lval_join(lval* x, lval* y) {
  int i;
  for (i = 0; i < y->count; i++) {
    x = lval_add(x, y->cell[i]);
  }
  free(y->cell);
  free(y);
  return x;
}

lval* lval_pop(lval* v, int i) {
  lval* x = v->cell[i];
  memmove(&v->cell[i],
    &v->cell[i+1], sizeof(lval*) * (v->count-i-1));
  v->count--;
  v->cell = realloc(v->cell, sizeof(lval*) * v->count);
  return x;
}

lval* lval_take(lval* v, int i) {
  lval* x = lval_pop(v, i);
  lval_del(v);
  return x;
}

void lval_print(lval* v);

void lval_print_expr(lval* v, char open, char close) {
  int i;
  putchar(open);
  for (i = 0; i < v->count; i++) {
    lval_print(v->cell[i]);
    if (i != (v->count-1)) {
      putchar(' ');
    }
  }
  putchar(close);
}

void lval_print_str(lval* v) {
  /* Make a Copy of the string */
  char* escaped = malloc(strlen(v->str)+1);
  strcpy(escaped, v->str);
  /* Pass it through the escape function */
  escaped = mpcf_escape(escaped);
  /* Print it between " characters */
  printf("\"%s\"", escaped);
  /* free the copied string */
  free(escaped);
}

void lval_print(lval* v) {
  switch (v->type) {
    case LVAL_FUN:
      if (v->builtin) {
        printf("<builtin>");
      } else {
        printf("(\\ ");
        lval_print(v->formals);
        putchar(' ');
        lval_print(v->body);
        putchar(')');
      }
    break;
    case LVAL_NUM:   printf("%li", v->num); break;
    case LVAL_ERR:   printf("Error: %s", v->err); break;
    case LVAL_SYM:   printf("%s", v->sym); break;
    case LVAL_STR:   lval_print_str(v); break;
    case LVAL_SEXPR: lval_print_expr(v, '(', ')'); break;
    case LVAL_QEXPR: lval_print_expr(v, '{', '}'); break;
  }
}

void lval_println(lval* v) { lval_print(v); putchar('\n'); }

int lval_eq(lval* x, lval* y) {
  int i;
  if (x->type != y->type) { return 0; }

  switch (x->type) {
    case LVAL_NUM: return (x->num == y->num);
    case LVAL_ERR: return (strcmp(x->err, y->err) == 0);
    case LVAL_SYM: return (strcmp(x->sym, y->sym) == 0);
    case LVAL_STR: return (strcmp(x->str, y->str) == 0);
    case LVAL_FUN:
      if (x->builtin || y->builtin) {
        return x->builtin == y->builtin;
      } else {
        return lval_eq(x->formals, y->formals) && lval_eq(x->body, y->body);
      }
    case LVAL_QEXPR:
    case LVAL_SEXPR:
      if (x->count != y->count) { return 0; }
      for (i = 0; i < x->count; i++) {
        if (!lval_eq(x->cell[i], y->cell[i])) { return 0; }
      }
      return 1;
    break;
  }
  return 0;
}

char* ltype_name(int t) {
  switch(t) {
    case LVAL_FUN: return "Function";
    case LVAL_NUM: return "Number";
    case LVAL_ERR: return "Error";
    case LVAL_SYM: return "Symbol";
    case LVAL_STR: return "String";
    case LVAL_SEXPR: return "S-Expression";
    case LVAL_QEXPR: return "Q-Expression";
    default: return "Unknown";
  }
}

/* Lisp Environment */

typedef struct HashEntry{
  char* sym;            // Symbol Name
  lval* val;            // Associated value
  struct HashEntry* next; // Linked list for collision resolution
} HashEntry;

typedef struct HashTable{
  struct HashEntry** buckets; // Array of pointers to hash entries
  int count;                  // Number of entries in the table
  int size;                   // Total number of bucketes
} HashTable;

struct lenv {
  lenv* par;        //Parent environment for "def"
  HashTable* table; //Hash table storing symbol - value pairs
};

/* New environmet with a hash table */

#define TABLE_SIZE 64

lenv* lenv_new() {
  // Allocate memory for the environment
  lenv* e = malloc(sizeof(lenv));
  if (!e){
    fprintf(stderr, "Error: Failed to allocate lenv\n");
    return NULL;
  }
  e->par = NULL; //Initialize parent to NULL
  //Allocate memory for the hash table
  e->table = malloc(sizeof(HashTable));
  if (!e->table){
    free(e);
    fprintf(stderr, "Error: Failed to allocate HashTable\n");
    return NULL;
  }
  e->table->count = 0; // Initialize entry count
  e->table->size = TABLE_SIZE; // Set initial table size
  // Allocate and zero-initialize buckets
  e->table->buckets = calloc(TABLE_SIZE, sizeof(HashEntry*));
  if (!e->table->buckets){
    free(e->table);
    free(e);
    fprintf(stderr, "Error: Failed to allocate buckets\n");
    return NULL;
  }
  return e;
}

/* Delete an environment and its hash table */
void lenv_del(lenv* e) {
  if (!e) return; // Guard against NULL pointer
  if (e->table){
    // Iterate through each bucket
    for (int i; i < e->table->size; i++){
        HashEntry* current = e->table->buckets[i];
        // Free each entry in the linked list
        while(current){
            HashEntry* temp = current;
            current = current->next;
            free(temp->sym); // Free symbol string
            lval_del(temp->val); // Free associated value
            free(temp); // Free entry
        }
    }
    free(e->table->buckets); //Free bucket array
    free(e->table); //Free hash table
  }
  free(e); //Free environment
}

/* Helper function to copy a hash table entry */
HashEntry* CopyNode(HashEntry* src){
  if (!src) return NULL; // Base case: no node to copy
  // Allocate new hash entry
  HashEntry* newNode = malloc(sizeof(HashEntry));
  if (!newNode){
    fprintf(stderr, "Memory allocation failed\n");
    return NULL;
  }
  //Copy symbol string
  newNode->sym = malloc(strlen(src->sym)+1);
  if (!newNode->sym){
    free(newNode);
    fprintf(stderr, "Memory allocation failed\n");
    return NULL;
  }
  strcpy(newNode->sym, src->sym);
  // Copy associated value
  newNode->val = lval_copy(src->val);
  if (!newNode->val){
    free(newNode->sym);
    free(newNode);
    fprintf(stderr, "Failed to copy value\n");
    return NULL;
  }
  // Recursively copy next node
  newNode->next = CopyNode(src->next);
  return newNode;
}

/* Copy an environment, including its hash table */
lenv* lenv_copy(lenv* e) {
  if (!e || !e->table || !e->table->buckets) return NULL; // Guard against invalid input
  // Allocate new environment
  lenv* n = malloc(sizeof(lenv));
  if (!n){
    fprintf(stderr, "Memory allocation failed for lenv\n");
    return NULL;
  }
  n->par = e->par; // Shallow copy of parent
  // Allocate new hash table
  n->table = malloc(sizeof(HashTable));
  if (!n->table){
    free(n);
    fprintf(stderr, "Memory allocation failed for HashTable\n");
    return NULL;
  }
  n->table->count = e->table->count; // Copy count
  n->table->size = e->table->size; // Copy size
  // Allocate bucket array
  n->table->buckets = calloc(n->table->size, sizeof(HashEntry*));
  if (!n->table->buckets){
    free(n->table);
    free(n);
    fprintf(stderr, "Memory allocation failed for HashTable\n");
    return NULL;
  }
  // Copy each bucket's linked list
  for (int i = 0; i < e->table->size; i++){
    if (e->table->buckets[i]){
        n->table->buckets[i] = CopyNode(e->table->buckets[i]);
        if (!n->table->buckets[i] && e->table->buckets[i]){
            lenv_del(n); // Cleanup on failure
            return NULL;
        }
    }
  }
  return n;
}

/* Hash function using SpookyHash */
unsigned int hash(const char* sym, int size){
  uint64 seed = 0;
  uint64 hash = spooky_Hash64(sym, strlen(sym), seed);
  unsigned int index = hash % size;
  return index;
}

/* Retrieve a value from the environment by symbol */
lval* lenv_get(lenv* e, lval* k) {
  // Validate inputs
  if (!e || !e->table || !e->table->buckets || !k || !k->sym || k->type != LVAL_SYM ){
    return lval_err("Invalid environment or symbol");
  }
  // Compute bucket index
  unsigned int index = hash(k->sym, e->table->size);
  HashEntry* current = e->table->buckets[index];
  // Search linked list for matching symbol
  while (current){
    if (strcmp(current->sym, k->sym) == 0){
        return lval_copy(current->val); // Return copy of value
    }
    current = current->next;
  }
  // Check parent environment if symbol not found
  if (e->par){
    return lenv_get(e->par, k);
  }
  return lval_err("Unbound Symbol '%s'", k->sym); // Symbol not found
}

/* Rehash the table when load factor exceeds threshold */
void rehash_table(lenv* e){
  // Store old buckets and size
  HashEntry** old_buckets = e->table->buckets;
  int old_size = e->table->size;
  // Double the table size
  e->table->size *= 2;
  // Allocate new bucket array
  e->table->buckets = calloc(e->table->size, sizeof(HashEntry*));
  if (!e->table->buckets){
    e->table->buckets = old_buckets;
    e->table->size = old_size;
    fprintf(stderr, "Error: Failed to rehash table\n");
    return;
  }
  // Rehash all Entries
  for (int i = 0; i < old_size; i++){
    HashEntry* current = old_buckets[i];
    while(current){
        HashEntry* next = current->next;
        unsigned int rhash_index = hash(current->sym, e->table->size);
        current->next = e->table->buckets[rhash_index];
        e->table->buckets[rhash_index] = current;
        current = next;
    }
  }
  free(old_buckets); //Free old bucket array
}

/* Store a symbol-value pair in the environment */
void lenv_put(lenv* e, lval* k, lval* v) {
  // Validate inputs
  if (!e || !e->table || !e->table->buckets || !k || !k->sym || !v || k->type != LVAL_SYM){
    fprintf(stderr, "Invalid environment or symbol\n");
    return;
  }
  // Compute bucket index
  unsigned int index = hash(k->sym, e->table->size);
  HashEntry* current = e->table->buckets[index];
  // Update existing symbol if found
  while (current){
    if (strcmp(current->sym, k->sym) == 0){
        lval_del(current->val);
        current->val = lval_copy(v);
        return;
    }
    current = current->next;
  }
  // Create new hash entry
  HashEntry* newvar = malloc(sizeof(HashEntry));
  if (!newvar){
    fprintf(stderr, "Failed to allocate HashEntry\n");
    return;
  }
  // Copy symbol string
  newvar->sym = malloc(strlen(k->sym) + 1);
  if (!newvar->sym){
    free(newvar);
    fprintf(stderr, "Failed to copy value\n");
    return;
  }
  strcpy(newvar->sym, k->sym);
  // Copy value
  newvar->val = lval_copy(v);
  if (!newvar->val){
    free(newvar->sym);
    free(newvar);
    fprintf(stderr, "Failed to copy value\n");
    return;
  }
  // Check for error value
  if (newvar->val->type == LVAL_ERR){
    lval_del(newvar->val);
    free(newvar->sym);
    free(newvar);
    fprintf(stderr, "Failed to copy value\n");
    return;
  }
  // Insert new entry
  newvar->next = e->table->buckets[index];
  e->table->buckets[index] = newvar;
  e->table->count++;
  // Rehash if load factor exceeds 0.75
  if (e->table->count > e->table->size * 0.75){
    rehash_table(e);
  }
}

/* Define a symbol in the global environment */
void lenv_def(lenv* e, lval* k, lval* v) {
  while (e->par) { e = e->par; } // Traverse to global environment
  lenv_put(e, k, v); // Store in global environment
}

/* Builtins */

/* Macro for argument validation */
#define LASSERT(args, cond, fmt, ...) \
  if (!(cond)) { lval* err = lval_err(fmt, ##__VA_ARGS__); lval_del(args); return err; }

/* Macro to check argument type */
#define LASSERT_TYPE(func, args, index, expect) \
  LASSERT(args, args->cell[index]->type == expect, \
    "Function '%s' passed incorrect type for argument %i. Got %s, Expected %s.", \
    func, index, ltype_name(args->cell[index]->type), ltype_name(expect))

/* Macro to check number of arguments */
#define LASSERT_NUM(func, args, num) \
  LASSERT(args, args->count == num, \
    "Function '%s' passed incorrect number of arguments. Got %i, Expected %i.", \
    func, args->count, num)

/* Macro to check for non-empty expression */
#define LASSERT_NOT_EMPTY(func, args, index) \
  LASSERT(args, args->cell[index]->count != 0, \
    "Function '%s' passed {} for argument %i.", func, index);

lval* lval_eval(lenv* e, lval* v);

/* Create a lambda function */
lval* builtin_lambda(lenv* e, lval* a) {
  int i;
  LASSERT_NUM("\\", a, 2); // Check for exactly 2 arguments
  LASSERT_TYPE("\\", a, 0, LVAL_QEXPR); // First arg must be Q-expression
  LASSERT_TYPE("\\", a, 1, LVAL_QEXPR); // Second arg must be Q-expression

  // Check that all formals are symbols
  for (i = 0; i < a->cell[0]->count; i++) {
    LASSERT(a, (a->cell[0]->cell[i]->type == LVAL_SYM),
      "Cannot define non-symbol. Got %s, Expected %s.",
      ltype_name(a->cell[0]->cell[i]->type), ltype_name(LVAL_SYM));
  }

  lval* formals = lval_pop(a, 0); // Extract formals
  lval* body = lval_pop(a, 0); // Extract body
  lval_del(a); // Delete arguments

  return lval_lambda(formals, body); // Create and return lambda
}

/* Convert an S-expression to a Q-expression */
lval* builtin_list(lenv* e, lval* a) {
  a->type = LVAL_QEXPR; // Change type to Q-expression
  return a; // Return modified lval
}

/* Get the first element of a Q-expression */
lval* builtin_head(lenv* e, lval* a) {
  LASSERT_NUM("head", a, 1); // Check for one argument
  LASSERT_TYPE("head", a, 0, LVAL_QEXPR); // Must be Q-expression
  LASSERT_NOT_EMPTY("head", a, 0); // Must not be empty

  lval* v = lval_take(a, 0); // Take the first elemen
  while (v->count > 1) { lval_del(lval_pop(v, 1)); } // Remove all but first
  return v; // Return first element
}

/* Get all but the first element of a Q-expression */
lval* builtin_tail(lenv* e, lval* a) {
  LASSERT_NUM("tail", a, 1); // Check for one argument
  LASSERT_TYPE("tail", a, 0, LVAL_QEXPR); // Must be Q-expression
  LASSERT_NOT_EMPTY("tail", a, 0); // Must not be empty

  lval* v = lval_take(a, 0); // Take the Q-expression
  lval_del(lval_pop(v, 0)); // Remove first element
  return v; // Return remaining elements
}

/* Evaluate a Q-expression as an S-expression */
lval* builtin_eval(lenv* e, lval* a) {
  LASSERT_NUM("eval", a, 1); // Check for one argument
  LASSERT_TYPE("eval", a, 0, LVAL_QEXPR); // Must be Q-expression

  lval* x = lval_take(a, 0); // Take the Q-expression
  x->type = LVAL_SEXPR; // Convert to S-expression
  return lval_eval(e, x); // Evaluate and return
}

/* Join multiple Q-expressions */
lval* builtin_join(lenv* e, lval* a) { // Each arg must be Q-expression
  int i;
  for (i = 0; i < a->count; i++) {
    LASSERT_TYPE("join", a, i, LVAL_QEXPR);
  }

  lval* x = lval_pop(a, 0); // Take first Q-expression

  while (a->count) {
    lval* y = lval_pop(a, 0); // Pop next Q-expression
    x = lval_join(x, y); // Join with x
  }

  lval_del(a); // Delete arguments
  return x; // Return joined Q-expression
}

/* Perform arithmetic operations */
lval* builtin_op(lenv* e, lval* a, char* op) {
  int i;
  for (i = 0; i < a->count; i++) {
    LASSERT_TYPE(op, a, i, LVAL_NUM); // Each arg must be a number
  }

  lval* x = lval_pop(a, 0); // Take first number

  if ((strcmp(op, "-") == 0) && a->count == 0) { x->num = -x->num; }

  while (a->count > 0) {
    lval* y = lval_pop(a, 0); // Pop next number

    if (strcmp(op, "+") == 0) { x->num += y->num; } // Addition
    if (strcmp(op, "-") == 0) { x->num -= y->num; } // Substraction
    if (strcmp(op, "*") == 0) { x->num *= y->num; } // Multiplication
    if (strcmp(op, "/") == 0) {
      if (y->num == 0) {
        lval_del(x); lval_del(y);
        x = lval_err("Division By Zero."); // Handle division by zero
        break;
      }
      x->num /= y->num; // Division
    }
    if (strcmp(op, "^") == 0) { x->num = pow(x->num, y->num); } // Power of

    lval_del(y); // Delete y
  }

  lval_del(a); // Delete arguments
  return x; // Return Result
}

/* Built-in arithmetic functions */
lval* builtin_add(lenv* e, lval* a) { return builtin_op(e, a, "+"); }
lval* builtin_sub(lenv* e, lval* a) { return builtin_op(e, a, "-"); }
lval* builtin_mul(lenv* e, lval* a) { return builtin_op(e, a, "*"); }
lval* builtin_div(lenv* e, lval* a) { return builtin_op(e, a, "/"); }
lval* builtin_pow(lenv* e, lval* a) { return builtin_op(e, a, "^"); }

/* Define or assign variables */
lval* builtin_var(lenv* e, lval* a, char* func) {
  int i;
  LASSERT_TYPE(func, a, 0, LVAL_QEXPR); // First arg must be Q-expression

  lval* syms = a->cell[0]; // Get symbols
  for (i = 0; i < syms->count; i++) {
    LASSERT(a, (syms->cell[i]->type == LVAL_SYM),
      "Function '%s' cannot define non-symbol. "
      "Got %s, Expected %s.",
      func, ltype_name(syms->cell[i]->type), ltype_name(LVAL_SYM)); // Check for symbols
  }

  LASSERT(a, (syms->count == a->count-1),
    "Function '%s' passed too many arguments for symbols. "
    "Got %i, Expected %i.",
    func, syms->count, a->count-1); // Check argument count

  for (i = 0; i < syms->count; i++) {
    if (strcmp(func, "def") == 0) { lenv_def(e, syms->cell[i], a->cell[i+1]); } // Global definition
    if (strcmp(func, "=")   == 0) { lenv_put(e, syms->cell[i], a->cell[i+1]); } // Local assignment
  }

  lval_del(a); // Delete arguments
  return lval_sexpr(); // Return empty S-expression
}

/* Built-in variable functions */
lval* builtin_def(lenv* e, lval* a) { return builtin_var(e, a, "def"); }
lval* builtin_put(lenv* e, lval* a) { return builtin_var(e, a, "="); }

/* Perform comparison operations */
lval* builtin_ord(lenv* e, lval* a, char* op) {
  LASSERT_NUM(op, a, 2); // Check for two arguments
  LASSERT_TYPE(op, a, 0, LVAL_NUM); // First arg must be number
  LASSERT_TYPE(op, a, 1, LVAL_NUM); // Second arg must be number

  int r;
  if (strcmp(op, ">")  == 0) { r = (a->cell[0]->num >  a->cell[1]->num); } // Greater than
  if (strcmp(op, "<")  == 0) { r = (a->cell[0]->num <  a->cell[1]->num); } // Less than
  if (strcmp(op, ">=") == 0) { r = (a->cell[0]->num >= a->cell[1]->num); } // Greater or equal
  if (strcmp(op, "<=") == 0) { r = (a->cell[0]->num <= a->cell[1]->num); } // Less or equal
  lval_del(a); // Delete arguments
  return lval_num(r); // Return result as number
}

/* Built-in comparison functions */
lval* builtin_gt(lenv* e, lval* a) { return builtin_ord(e, a, ">");  }
lval* builtin_lt(lenv* e, lval* a) { return builtin_ord(e, a, "<");  }
lval* builtin_ge(lenv* e, lval* a) { return builtin_ord(e, a, ">="); }
lval* builtin_le(lenv* e, lval* a) { return builtin_ord(e, a, "<="); }

/* Perform equality comparisons */
lval* builtin_cmp(lenv* e, lval* a, char* op) {
  LASSERT_NUM(op, a, 2); // Check for two arguments
  int r;
  if (strcmp(op, "==") == 0) { r =  lval_eq(a->cell[0], a->cell[1]); } // Equality
  if (strcmp(op, "!=") == 0) { r = !lval_eq(a->cell[0], a->cell[1]); } // Inequality
  lval_del(a); // Delete arguments
  return lval_num(r); // Return result as number
}

/* Built-in equality functions */
lval* builtin_eq(lenv* e, lval* a) { return builtin_cmp(e, a, "=="); }
lval* builtin_ne(lenv* e, lval* a) { return builtin_cmp(e, a, "!="); }

/* Conditional evaluation */
lval* builtin_if(lenv* e, lval* a) {
  LASSERT_NUM("if", a, 3); // Check for three arguments
  LASSERT_TYPE("if", a, 0, LVAL_NUM); // Condition must be number
  LASSERT_TYPE("if", a, 1, LVAL_QEXPR); // Then branch must be Q-expression
  LASSERT_TYPE("if", a, 2, LVAL_QEXPR); // Else branch must be Q-expression

  lval* x;
  a->cell[1]->type = LVAL_SEXPR; // Convert then branch to S-expression
  a->cell[2]->type = LVAL_SEXPR; // Convert else branch to S-expression

  if (a->cell[0]->num) {
    x = lval_eval(e, lval_pop(a, 1)); // Evaluate then branch
  } else {
    x = lval_eval(e, lval_pop(a, 2)); // Evaluate else branch
  }

  lval_del(a); // Delete arguments
  return x; // Return result
}

/* Forward declaration for lval_read */
lval* lval_read(mpc_ast_t* t);

/* Load and evaluate a file */
lval* builtin_load(lenv* e, lval* a) {
  LASSERT_NUM("load", a, 1);
  LASSERT_TYPE("load", a, 0, LVAL_STR);

  /* Parse File given by string name */
  mpc_result_t r;
  if (mpc_parse_contents(a->cell[0]->str, Lispy, &r)) {

    /* Read contents */
    lval* expr = lval_read(r.output);
    mpc_ast_delete(r.output);

    /* Evaluate each Expression */
    while (expr->count) {
      lval* x = lval_eval(e, lval_pop(expr, 0));
      /* If Evaluation leads to error print it */
      if (x->type == LVAL_ERR) { lval_println(x); }
      lval_del(x);
    }

    /* Delete expressions and arguments */
    lval_del(expr);
    lval_del(a);

    /* Return empty list */
    return lval_sexpr();

  } else {
    /* Get Parse Error as String */
    char* err_msg = mpc_err_string(r.error);
    mpc_err_delete(r.error);

    /* Create new error message using it */
    lval* err = lval_err("Could not load Library %s", err_msg);
    free(err_msg);
    lval_del(a);

    /* Cleanup and return error */
    return err;
  }
}

/* Print arguments */
lval* builtin_print(lenv* e, lval* a) {
  int i;

  /* Print each argument followed by a space */
  for (i = 0; i < a->count; i++) {
    lval_print(a->cell[i]); putchar(' '); // Print each argument
  }

  /* Print a newline and delete arguments */
  putchar('\n');
  lval_del(a);

  return lval_sexpr();
}

lval* builtin_error(lenv* e, lval* a) {
  LASSERT_NUM("error", a, 1);
  LASSERT_TYPE("error", a, 0, LVAL_STR);

  /* Construct Error from first argument */
  lval* err = lval_err(a->cell[0]->str);

  /* Delete arguments and return */
  lval_del(a);
  return err;
}

/* Add a built-in function to the environment */
void lenv_add_builtin(lenv* e, char* name, lbuiltin func) {
  lval* k = lval_sym(name); // Create symbol lval
  lval* v = lval_builtin(func); // Create function lval
  lenv_put(e, k, v); // Store in environment
  lval_del(k); lval_del(v); // Delete lvals
}

/* Register all built-in functions */
void lenv_add_builtins(lenv* e) {
  /* Variable Functions */
  lenv_add_builtin(e, "\\",  builtin_lambda);
  lenv_add_builtin(e, "def", builtin_def);
  lenv_add_builtin(e, "=",   builtin_put);

  /* List Functions */
  lenv_add_builtin(e, "list", builtin_list);
  lenv_add_builtin(e, "head", builtin_head);
  lenv_add_builtin(e, "tail", builtin_tail);
  lenv_add_builtin(e, "eval", builtin_eval);
  lenv_add_builtin(e, "join", builtin_join);

  /* Mathematical Functions */
  lenv_add_builtin(e, "+", builtin_add);
  lenv_add_builtin(e, "-", builtin_sub);
  lenv_add_builtin(e, "*", builtin_mul);
  lenv_add_builtin(e, "/", builtin_div);
  lenv_add_builtin(e, "^", builtin_pow);

  /* Comparison Functions */
  lenv_add_builtin(e, "if", builtin_if);
  lenv_add_builtin(e, "==", builtin_eq);
  lenv_add_builtin(e, "!=", builtin_ne);
  lenv_add_builtin(e, ">",  builtin_gt);
  lenv_add_builtin(e, "<",  builtin_lt);
  lenv_add_builtin(e, ">=", builtin_ge);
  lenv_add_builtin(e, "<=", builtin_le);

  /* String Functions */
  lenv_add_builtin(e, "load",  builtin_load);
  lenv_add_builtin(e, "error", builtin_error);
  lenv_add_builtin(e, "print", builtin_print);
}

/* Evaluation */

/* Call a function with arguments */
lval* lval_call(lenv* e, lval* f, lval* a) {

  if (f->builtin) { return f->builtin(e, a); } // Call built-in function

  int given = a->count; // Number of arguments provided
  int total = f->formals->count; // Number of expected arguments

  while (a->count) {

    if (f->formals->count == 0) {
      lval_del(a);
      return lval_err("Function passed too many arguments. "
        "Got %i, Expected %i.", given, total); // Too many arguments
    }

    lval* sym = lval_pop(f->formals, 0); // Pop formal parameter

    if (strcmp(sym->sym, "&") == 0) {

      if (f->formals->count != 1) {
        lval_del(a);
        return lval_err("Function format invalid. "
          "Symbol '&' not followed by single symbol."); // Invalid rest parameter
      }

      lval* nsym = lval_pop(f->formals, 0); // Get rest parameter symbol
      lenv_put(f->env, nsym, builtin_list(e, a)); // Bind remaining args as list
      lval_del(sym); lval_del(nsym);
      break;
    }

    lval* val = lval_pop(a, 0); // Pop argument
    lenv_put(f->env, sym, val); // Bind argument to parameter
    lval_del(sym); lval_del(val);
  }

  lval_del(a); // Delete arguments

  if (f->formals->count > 0 &&
    strcmp(f->formals->cell[0]->sym, "&") == 0) {

    if (f->formals->count != 2) {
      return lval_err("Function format invalid. "
        "Symbol '&' not followed by single symbol."); // Invalid rest parameter
    }

    lval_del(lval_pop(f->formals, 0)); // Remove &

    lval* sym = lval_pop(f->formals, 0); // Get rest parameter symbol
    lval* val = lval_qexpr(); // Create empty Q-expression
    lenv_put(f->env, sym, val); // Bind empty list
    lval_del(sym); lval_del(val);
  }

  if (f->formals->count == 0) {
    f->env->par = e; // Set parent environment
    return builtin_eval(f->env, lval_add(lval_sexpr(), lval_copy(f->body))); // Evaluate body
  } else {
    return lval_copy(f); // Return partial application
  }

}

/* Evaluate an S-expression */
lval* lval_eval_sexpr(lenv* e, lval* v) {
  int i;
  for (i = 0; i < v->count; i++) { v->cell[i] = lval_eval(e, v->cell[i]); } // Evaluate each sub-expression
  for (i = 0; i < v->count; i++) { if (v->cell[i]->type == LVAL_ERR) { return lval_take(v, i); } } // Return error if any

  if (v->count == 0) { return v; } // Empty expression
  if (v->count == 1) { return lval_eval(e, lval_take(v, 0)); } // Single expression

  lval* f = lval_pop(v, 0); // Pop function
  if (f->type != LVAL_FUN) {
    lval* err = lval_err(
      "S-Expression starts with incorrect type. "
      "Got %s, Expected %s.",
      ltype_name(f->type), ltype_name(LVAL_FUN)); // Invalid function
    lval_del(f); lval_del(v);
    return err;
  }

  lval* result = lval_call(e, f, v); // Call function
  lval_del(f); // Delete function
  return result; // Return result
}

/* Evaluate an lval */
lval* lval_eval(lenv* e, lval* v) {
  if (v->type == LVAL_SYM) {
    lval* x = lenv_get(e, v); // Look up symbol
    lval_del(v);
    return x; // Return value
  }
  if (v->type == LVAL_SEXPR) { return lval_eval_sexpr(e, v); } // Evaluate S-expression
  return v; // Return unchanged
}

/* Reading */

/* Read a number from AST */
lval* lval_read_num(mpc_ast_t* t) {
  errno = 0;
  long x = strtol(t->contents, NULL, 10); // Convert string to number
  return errno != ERANGE ? lval_num(x) : lval_err("Invalid Number."); // Return number or error
}

/* Read a string from AST */
lval* lval_read_str(mpc_ast_t* t) {
  /* Cut off the final quote character */
  t->contents[strlen(t->contents)-1] = '\0';
  /* Copy the string missing out the first quote character */
  char* unescaped = malloc(strlen(t->contents+1)+1);
  strcpy(unescaped, t->contents+1);
  /* Pass through the unescape function */
  unescaped = mpcf_unescape(unescaped);
  /* Construct a new lval using the string */
  lval* str = lval_str(unescaped);
  /* Free the string and return */
  free(unescaped);
  return str;
}

/* Read an AST into an lval */
lval* lval_read(mpc_ast_t* t) {
  int i;
  if (strstr(t->tag, "number")) { return lval_read_num(t); } // Read number
  if (strstr(t->tag, "string")) { return lval_read_str(t); } // Read string
  if (strstr(t->tag, "symbol")) { return lval_sym(t->contents); } // Read symbol

  lval* x = NULL;
  if (strcmp(t->tag, ">") == 0) { x = lval_sexpr(); } // Root node
  if (strstr(t->tag, "sexpr"))  { x = lval_sexpr(); } // S-expression
  if (strstr(t->tag, "qexpr"))  { x = lval_qexpr(); } // Q-expression

  for (i = 0; i < t->children_num; i++) {
    if (strcmp(t->children[i]->contents, "(") == 0) { continue; } // Skip parentheses
    if (strcmp(t->children[i]->contents, ")") == 0) { continue; }
    if (strcmp(t->children[i]->contents, "}") == 0) { continue; }
    if (strcmp(t->children[i]->contents, "{") == 0) { continue; }
    if (strcmp(t->children[i]->tag,  "regex") == 0) { continue; } // Skip regex
    if (strstr(t->children[i]->tag, "comment")) { continue; } // Skip comments
    x = lval_add(x, lval_read(t->children[i])); // Add child to expression
  }

  return x; // Return lval
}

/* Main */

int main(int argc, char** argv) {
  /* Initialize parsers */
  Number  = mpc_new("number");
  Symbol  = mpc_new("symbol");
  String  = mpc_new("string");
  Comment = mpc_new("comment");
  Sexpr   = mpc_new("sexpr");
  Qexpr   = mpc_new("qexpr");
  Expr    = mpc_new("expr");
  Lispy   = mpc_new("lispy");
  /* Define grammar */
  mpca_lang(MPCA_LANG_DEFAULT,
    "                                              \
      number  : /-?[0-9]+/ ;                       \
      symbol  : /[a-zA-Z0-9_+\\-*\\/\\\\=<>!&^]+/ ; \
      string  : /\"(\\\\.|[^\"])*\"/ ;             \
      comment : /;[^\\r\\n]*/ ;                    \
      sexpr   : '(' <expr>* ')' ;                  \
      qexpr   : '{' <expr>* '}' ;                  \
      expr    : <number>  | <symbol> | <string>    \
              | <comment> | <sexpr>  | <qexpr>;    \
      lispy   : /^/ <expr>* /$/ ;                  \
    ",
    Number, Symbol, String, Comment, Sexpr, Qexpr, Expr, Lispy);

  lenv* e = lenv_new(); // Create new environment
  lenv_add_builtins(e); // Register built-in functions

  /* Interactive Prompt */
  if (argc == 1) {

    puts("Lispy Version 0.0.0.1.0"); // Print version
    puts("Press Ctrl+c to Exit\n"); // Print exit instruction

    while (1) {

      char* input = readline("lispy> "); // Read input
      add_history(input); // Add to history

      mpc_result_t r;
      if (mpc_parse("<stdin>", input, Lispy, &r)) { // Add to history

        lval* x = lval_eval(e, lval_read(r.output)); // Evaluate AST
        lval_println(x); // Print result
        lval_del(x); // Delete result

        mpc_ast_delete(r.output); // Delete AST
      } else {
        mpc_err_print(r.error); // Print parse error
        mpc_err_delete(r.error); // Delete error
      }

      free(input); // Free input

    }
  }

  /* Supplied with list of files */
  if (argc >= 2) {
  	int i;

    /* loop over each supplied filename (starting from 1) */
    for (i = 1; i < argc; i++) {

      /* Argument list with a single argument, the filename */
      lval* args = lval_add(lval_sexpr(), lval_str(argv[i]));

      /* Pass to builtin load and get the result */
      lval* x = builtin_load(e, args);

      /* If the result is an error be sure to print it */
      if (x->type == LVAL_ERR) { lval_println(x); }
      lval_del(x);
    }
  }

  lenv_del(e); // Delete environment
  /* Clean up parsers */
  mpc_cleanup(8,
    Number, Symbol, String, Comment,
    Sexpr,  Qexpr,  Expr,   Lispy);

  return 0; // Exit
}

