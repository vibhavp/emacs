#include <config.h>
#include <assert.h>

#include <libgccjit.h>
#include <stdarg.h>

#include "lisp.h"
#include "syntax.h"
#include "buffer.h"
#include "bytecode.h"
#include "keyboard.h"
#include "dispextern.h"
#include "jit.h"

#define FETCH (*pc++)
#define FETCH2 (op = FETCH, op + (FETCH << 8))
#define JIT_ADD_COMMENT(c) gcc_jit_block_add_comment (ctxt->cur_block, NULL, (c))
#define JIT_ADD_COMMENT_BLOCK(b, c) gcc_jit_block_add_comment ((b), NULL, (c))


enum jit_block_type
  {
   JIT_BLOCK,
   JIT_BLOCK_IF,
   JIT_BLOCK_ELSE,
   JIT_BLOCK_LOOP
  };

struct jit_block
{
  enum jit_block_type type;

  gcc_jit_block *continuation_block;

  union {
    /* if type == JIT_BLOCK_IF, then this is the else block that shuold be used
     * while compiling the else section. */
    gcc_jit_block *else_block;
    /* if type == JIT_BLOCK, this is the block that needs to be patched with
     * a jump to continuation_block once it has ended. */
    gcc_jit_block *br_if_true_block;
    /* if type == JIT_BLOCK_LOOP, this is the block that needs to be patched
     * a jump to continuation_block once it has ended. */
    gcc_jit_block *loop_end_block;
  };
};

struct jit_block_stack
{
  struct jit_block **stack;
  int top;
  int len;
};


/*
struct
{
  Lisp_Object car;           (s_fields[0])
  union
  {
    Lisp_Object cdr;         (u_fields[0])
    struct Lisp_Cons *chain; (u_fields[1])
  } u;                       (s_fields[1])
} s;
*/

#define Bif 0270
#define Belse 0271
#define Bend 0272

#define Bloop 0273
#define Bbr 0274
#define Bbrif 0275
#define Bblock 0276

static struct jit_block_stack *
jit_block_stack_new (void)
{
  struct jit_block_stack *stack = xmalloc (sizeof
                                           (struct jit_block_stack));
  stack->top = -1;
  stack->len = 0;
  return stack;
}

static struct jit_block *
jit_block_stack_push_new (struct jit_block_stack *stack)
{
  stack->top++;
  if (stack->len == 0)
    {
      stack->stack = xmalloc (sizeof (struct jit_block *));
      stack->stack[0] = xmalloc (sizeof (struct jit_block));
      stack->len = 1;
    }
  else
    {
      if (stack->top == stack->len)
        {
          stack->stack = xrealloc (stack->stack,
                                   sizeof (struct jit_block *) * ++stack->len);
          stack->stack[stack->top] = xmalloc (sizeof (struct jit_block));
        }
    }

  return stack->stack[stack->top];
}

static struct jit_block *
jit_block_stack_push_if (struct jit_block_stack *stack,
                         gcc_jit_block *else_block, gcc_jit_block *final_block)
{

  struct jit_block *block = jit_block_stack_push_new (stack);
  block->type = JIT_BLOCK_IF;
  block->continuation_block = final_block;
  block->else_block = else_block;
  return block;
}

static struct jit_block *
jit_block_stack_push_loop (struct jit_context *ctxt,
                           struct jit_block_stack *stack)
{
  struct jit_block *block = jit_block_stack_push_new (stack);
  block->type = JIT_BLOCK_LOOP;
  block->continuation_block = gcc_jit_function_new_block (ctxt->cur_func,
                                                          "loop_start");
  return block;
}

static struct jit_block *
jit_block_stack_push_regular_block (struct jit_context *ctxt,
                                    struct jit_block_stack *stack)
{
  struct jit_block *block = jit_block_stack_push_new (stack);
  block->type = JIT_BLOCK;
  block->continuation_block = gcc_jit_function_new_block (ctxt->cur_func, "block");
  return block;
}

static struct jit_block *
jit_block_stack_pop (struct jit_block_stack *stack)
{
  eassert (stack->top >= 0);
  return stack->stack[stack->top--];
}

static struct jit_block *
jit_block_stack_top (struct jit_block_stack *stack)
{
  eassert (stack->top >= 0);
  return stack->stack[stack->top];
}

static void
jit_block_stack_free (struct jit_block_stack *stack)
{
  int i;
  for (i = 0; i < stack->len; i++)
      xfree (stack->stack[i]);
}

static gcc_jit_lvalue *
jit_new_local (struct jit_context *ctxt, gcc_jit_type *type)
{
  char buf[15];
  sprintf (buf, "local%lu", ctxt->local_index++);
  return gcc_jit_function_new_local (ctxt->cur_func, NULL, type, buf);
}

static gcc_jit_rvalue *
jit_new_rvalue_from_ptrdiff_t (struct jit_context *ctxt, ptrdiff_t v)
{
  if (sizeof (ptrdiff_t) == sizeof (int)
      || sizeof (ptrdiff_t) == sizeof (short int))
    return gcc_jit_context_new_rvalue_from_int (ctxt->ctxt,
                                                ctxt->type_ptrdiff_t, v);
  return gcc_jit_context_new_rvalue_from_long (ctxt->ctxt,
                                               ctxt->type_ptrdiff_t,
                                               v);
}

static void
jit_compile_block_unreachable (struct jit_context *ctxt, gcc_jit_block *block)
{
  gcc_jit_function *unreachable =
    gcc_jit_context_get_builtin_function (ctxt->ctxt, "__builtin_unreachable");
  gcc_jit_rvalue *call =
    gcc_jit_context_new_call(ctxt->ctxt, NULL, unreachable, 0, NULL);
  gcc_jit_block_add_eval (block, NULL, call);
}

/* Compile call to a subroutine that takes args Lisp_Object arguments,
   and returns a Lisp_Object value */
static gcc_jit_rvalue *
jit_compile_call_to_subr (struct jit_context *ctxt,
                          void *subr, int nargs,
                          ...)
{
  USE_SAFE_ALLOCA;
  va_list ap;
  gcc_jit_type **args_types = SAFE_ALLOCA (sizeof (gcc_jit_type *) * nargs);
  int i;

  for (i = 0; i < nargs; i++)
    args_types[i] = ctxt->type_lisp_object;

  gcc_jit_type *ptr_type =
    gcc_jit_context_new_function_ptr_type (ctxt->ctxt, NULL,
                                           ctxt->type_lisp_object, nargs,
                                           args_types, 0);
  gcc_jit_rvalue *fn_ptr =
    gcc_jit_context_new_rvalue_from_ptr (ctxt->ctxt, ptr_type,
                                         subr);
  gcc_jit_rvalue **args = SAFE_ALLOCA (sizeof (gcc_jit_rvalue *) * nargs);

  va_start (ap, nargs);
  for (i = 0; i < nargs; i++)
    args[i] = va_arg (ap, gcc_jit_rvalue *);
  va_end (ap);

  gcc_jit_rvalue *call =
    gcc_jit_context_new_call_through_ptr (ctxt->ctxt, NULL, fn_ptr, nargs,
                                          args);
  SAFE_FREE ();
  return call;
}

static gcc_jit_rvalue *
jit_compile_cast_to (struct jit_context *ctxt, gcc_jit_rvalue *v1,
                     gcc_jit_type *to)
{
  gcc_jit_type *from = gcc_jit_rvalue_get_type(v1);
  gcc_jit_field *fields[2] = {gcc_jit_context_new_field (ctxt->ctxt, NULL, to,
                                                         "to"),
                              gcc_jit_context_new_field (ctxt->ctxt, NULL, from,
                                                         "from")};
  gcc_jit_type *union_type = gcc_jit_context_new_union_type (ctxt->ctxt, NULL,
                                                             "cast_union", 2,
                                                             fields);
  gcc_jit_lvalue *v2 = jit_new_local (ctxt, union_type);
  gcc_jit_block_add_assignment (ctxt->cur_block, NULL,
                                gcc_jit_lvalue_access_field(v2, NULL, fields[1]),
                                v1);
  return gcc_jit_rvalue_access_field (gcc_jit_lvalue_as_rvalue (v2), NULL,
                                      fields[0]);
}

static gcc_jit_rvalue *
jit_compile_call_to_many_subr (struct jit_context *ctxt,  ptrdiff_t nargs,
                               gcc_jit_lvalue **var_stack, int stack_top,
                               gcc_jit_rvalue *scratch,
                               Lisp_Object (*subr)(ptrdiff_t, Lisp_Object *))
{
  int i, top = stack_top;

  gcc_jit_type *lo_ptr_type = gcc_jit_type_get_pointer (ctxt->type_lisp_object),
    *param_types[2] = {ctxt->type_ptrdiff_t, lo_ptr_type},
    *ptr_type = gcc_jit_context_new_function_ptr_type (ctxt->ctxt, NULL,
                                                       ctxt->type_lisp_object,
                                                       2, param_types, 0),
    *type_int = gcc_jit_context_get_type (ctxt->ctxt, GCC_JIT_TYPE_INT);
  for (i = nargs - 1; i >= 0; i--)
    {
      gcc_jit_rvalue *index = gcc_jit_context_new_rvalue_from_int (ctxt->ctxt,
                                                                   type_int, i);
      gcc_jit_lvalue *access = gcc_jit_context_new_array_access (ctxt->ctxt,
                                                                 NULL,
                                                                 scratch,
                                                                 index);
      gcc_jit_rvalue *val = gcc_jit_lvalue_as_rvalue (var_stack[top--]);
      gcc_jit_block_add_assignment (ctxt->cur_block, NULL, access, val);
    }
  gcc_jit_rvalue *fn_ptr = gcc_jit_context_new_rvalue_from_ptr (ctxt->ctxt,
                                                                ptr_type, subr),
    *args[2] = {jit_new_rvalue_from_ptrdiff_t (ctxt, nargs), scratch};
  gcc_jit_rvalue *call = gcc_jit_context_new_call_through_ptr (ctxt->ctxt, NULL,
                                                               fn_ptr, 2, args);
  return call;
}

static void
jit_compile_assign_ternary (struct jit_context *ctxt, gcc_jit_rvalue *bool_val,
                            gcc_jit_lvalue *lval, gcc_jit_rvalue *when_true,
                            gcc_jit_rvalue *when_false,
                            gcc_jit_block **cur_block)
{
  gcc_jit_block *true_block = gcc_jit_function_new_block (ctxt->cur_func, "when_true"),
    *false_block = gcc_jit_function_new_block (ctxt->cur_func, "when_false"),
    *final_block = gcc_jit_function_new_block (ctxt->cur_func, "final");

  gcc_jit_block_end_with_conditional (*cur_block, NULL, bool_val, true_block,
                                      false_block);
  gcc_jit_block_add_assignment (true_block, NULL, lval, when_true);
  gcc_jit_block_end_with_jump (true_block, NULL, final_block);

  gcc_jit_block_add_assignment (false_block, NULL, lval, when_false);
  gcc_jit_block_end_with_jump (false_block, NULL, final_block);

  *cur_block = final_block;
}

static gcc_jit_rvalue *
jit_compile_XLP (struct jit_context *ctxt, gcc_jit_rvalue *o)
{
  gcc_jit_rvalue *res;
  gcc_jit_type *type_uintptr = gcc_jit_context_get_int_type (ctxt->ctxt,
                                                             sizeof(uintptr_t),
                                                             0);
  if (CHECK_LISP_OBJECT_TYPE)
    o = gcc_jit_rvalue_access_field (o, NULL, ctxt->field_lisp_object);

  if (LISP_WORDS_ARE_POINTERS)
    res = jit_compile_cast_to (ctxt, o, ctxt->type_void_ptr);
  else
    {
      res = jit_compile_cast_to (ctxt, o, type_uintptr);
      res = jit_compile_cast_to (ctxt, res, ctxt->type_void_ptr);
    }

  return res;
}

static gcc_jit_rvalue *
jit_new_rvalue_from_emacs_int (struct jit_context *ctxt, EMACS_INT i)
{
  if (JIT_TYPE_EMACS_INT == GCC_JIT_TYPE_INT)
    return gcc_jit_context_new_rvalue_from_int (ctxt->ctxt,
                                                ctxt->type_emacs_int, i);

  return gcc_jit_context_new_rvalue_from_long (ctxt->ctxt,
                                               ctxt->type_emacs_int, i);
}

static gcc_jit_rvalue *
jit_new_rvalue_from_emacs_uint (struct jit_context *ctxt, EMACS_UINT i)
{
  if (JIT_TYPE_EMACS_INT == GCC_JIT_TYPE_INT)
    return gcc_jit_context_new_rvalue_from_int (ctxt->ctxt,
                                                ctxt->type_emacs_uint,
                                                i);

  return gcc_jit_context_new_rvalue_from_long (ctxt->ctxt,
                                               ctxt->type_emacs_uint, i);
}

static gcc_jit_rvalue *
jit_compile_XLI (struct jit_context *ctxt, gcc_jit_rvalue *o, bool emacs_uint)
{
  gcc_jit_rvalue *xli;

  if (CHECK_LISP_OBJECT_TYPE)
    {
      xli = gcc_jit_rvalue_access_field (o, NULL, ctxt->field_lisp_object);

      if (LISP_WORDS_ARE_POINTERS)
          xli = jit_compile_cast_to (ctxt, xli, ctxt->type_emacs_int);
    }
  else
    {
      if (LISP_WORDS_ARE_POINTERS)
        xli =  jit_compile_cast_to (ctxt, o, ctxt->type_emacs_int);
      else
        xli = o;
    }

  if (emacs_uint)
    return gcc_jit_context_new_cast (ctxt->ctxt, NULL, xli,
                                     ctxt->type_emacs_uint);

  return xli;
}

static gcc_jit_rvalue *
jit_compile_XIL (struct jit_context *ctxt, gcc_jit_rvalue *o)
{
  return jit_compile_cast_to (ctxt, o, ctxt->type_lisp_object);
}

static gcc_jit_rvalue *
jit_new_rvalue_from_lisp_object (struct jit_context *ctxt, Lisp_Object o)
{
  gcc_jit_rvalue *word;

  if (LISP_WORDS_ARE_POINTERS)
    word = gcc_jit_context_new_rvalue_from_ptr (ctxt->ctxt,
                                                ctxt->type_lisp_word,
                                                XLP (o));
  else
    word = jit_new_rvalue_from_emacs_int (ctxt, XLI (o));

  if (CHECK_LISP_OBJECT_TYPE)
    {
      gcc_jit_lvalue *o = jit_new_local (ctxt, ctxt->type_lisp_object),
        *field = gcc_jit_lvalue_access_field (o, NULL, ctxt->field_lisp_object);
      gcc_jit_block_add_assignment (ctxt->cur_block, NULL, field, word);
      return gcc_jit_lvalue_as_rvalue (o);
    }
  return word;
}

static gcc_jit_rvalue *
jit_compile_XTYPE (struct jit_context *ctxt, gcc_jit_rvalue *v)
{
  gcc_jit_rvalue *xli = jit_compile_XLI (ctxt, v, false);

  if (USE_LSB_TAG) {
    gcc_jit_rvalue *i = jit_new_rvalue_from_emacs_int (ctxt, ~VALMASK);
    return gcc_jit_context_new_binary_op (ctxt->ctxt, NULL,
                                          GCC_JIT_BINARY_OP_BITWISE_AND,
                                          ctxt->type_lisp_type, xli, i);
  }

  gcc_jit_rvalue *i = jit_new_rvalue_from_emacs_int (ctxt, VALBITS);
  return gcc_jit_context_new_binary_op (ctxt->ctxt, NULL,
                                        GCC_JIT_BINARY_OP_RSHIFT,
                                        ctxt->type_lisp_type,
                                        xli, i);
}

static gcc_jit_rvalue *
jit_compile_XUNTAG (struct jit_context *ctxt, gcc_jit_rvalue *o, int type,
                    gcc_jit_type *ctype)
{
  gcc_jit_type *type_char_ptr =
    gcc_jit_type_get_pointer (gcc_jit_context_get_type (ctxt->ctxt,
                                                         GCC_JIT_TYPE_CHAR)),
    *type_int = gcc_jit_context_get_type (ctxt->ctxt, GCC_JIT_TYPE_INT);
  gcc_jit_rvalue *index =
    gcc_jit_context_new_rvalue_from_long (ctxt->ctxt,
                                          type_int,
                                          - LISP_WORD_TAG (type));
  gcc_jit_rvalue *xlp = gcc_jit_context_new_cast (ctxt->ctxt, NULL,
                                                  jit_compile_XLP (ctxt, o),
                                                  type_char_ptr);
  gcc_jit_lvalue *xlp_l = gcc_jit_context_new_array_access (ctxt->ctxt, NULL, xlp,
                                                            index);
  xlp = gcc_jit_lvalue_get_address (xlp_l, NULL);
  return jit_compile_cast_to (ctxt, xlp, ctype);
}

static gcc_jit_rvalue *
jit_compile_EQ(struct jit_context *ctxt, gcc_jit_rvalue *v1,
               gcc_jit_rvalue *v2)
{
  return gcc_jit_context_new_comparison (ctxt->ctxt, NULL,
                                         GCC_JIT_COMPARISON_EQ, v1, v2);
}

static gcc_jit_rvalue *
jit_compile_NEQ(struct jit_context *ctxt, gcc_jit_rvalue *v1,
                gcc_jit_rvalue *v2)
{
  return gcc_jit_context_new_comparison (ctxt->ctxt, NULL,
                                         GCC_JIT_COMPARISON_NE, v1, v2);
}

static gcc_jit_rvalue *
jit_compile_NILP (struct jit_context *ctxt, gcc_jit_rvalue *v1)
{
  return jit_compile_EQ (ctxt, v1, ctxt->rvalue_nil);
}

static gcc_jit_rvalue *
jit_compile_not_NILP (struct jit_context *ctxt, gcc_jit_rvalue *v1)
{
  return jit_compile_NEQ (ctxt, v1, ctxt->rvalue_nil);
}

static gcc_jit_rvalue *
jit_compile_CONSP (struct jit_context *ctxt, gcc_jit_rvalue *o)
{
  gcc_jit_type *typ = gcc_jit_context_get_type (ctxt->ctxt, GCC_JIT_TYPE_INT);
  gcc_jit_rvalue *v1 = gcc_jit_context_new_rvalue_from_int (ctxt->ctxt, typ,
                                                            Lisp_Cons);
  return gcc_jit_context_new_comparison (ctxt->ctxt, NULL,
                                         GCC_JIT_COMPARISON_EQ,
                                         jit_compile_XTYPE (ctxt, o), v1);
}

static gcc_jit_rvalue *
jit_compile_LISTP (struct jit_context *ctxt, gcc_jit_rvalue *o)
{
  gcc_jit_rvalue *consp = jit_compile_CONSP (ctxt, o),
    *nilp = jit_compile_NILP (ctxt, o);
  return gcc_jit_context_new_binary_op (ctxt->ctxt, NULL,
                                        GCC_JIT_BINARY_OP_LOGICAL_OR,
                                        ctxt->type_bool, consp, nilp);
}

static gcc_jit_rvalue *
jit_compile_FUNCTIONP (struct jit_context *ctxt, gcc_jit_rvalue *o)
{
  gcc_jit_type *bool_type = gcc_jit_context_get_type (ctxt->ctxt, GCC_JIT_TYPE_BOOL);
  gcc_jit_type *fn_type =
    gcc_jit_context_new_function_ptr_type (ctxt->ctxt, NULL, bool_type, 1,
                                           &ctxt->type_lisp_object, 0);
  gcc_jit_rvalue *fn_ptr =
    gcc_jit_context_new_rvalue_from_ptr (ctxt->ctxt, fn_type, FUNCTIONP);

  return gcc_jit_context_new_call_through_ptr (ctxt->ctxt, NULL, fn_ptr, 1,
                                               &o);
}

static gcc_jit_rvalue *
jit_compile_STRINGP (struct jit_context *ctxt, gcc_jit_rvalue *o)
{
  gcc_jit_type *typ = gcc_jit_context_get_type (ctxt->ctxt, GCC_JIT_TYPE_INT);
  gcc_jit_rvalue *v1 = gcc_jit_context_new_rvalue_from_int (ctxt->ctxt, typ,
                                                            Lisp_String);
  return gcc_jit_context_new_comparison (ctxt->ctxt, NULL, GCC_JIT_COMPARISON_EQ,
                                         jit_compile_XTYPE (ctxt, o), v1);
}

static gcc_jit_rvalue *
jit_compile_FIXNUMP (struct jit_context *ctxt, gcc_jit_rvalue *o)
{
  gcc_jit_type *int_type = gcc_jit_context_get_type (ctxt->ctxt,
                                                     GCC_JIT_TYPE_INT);
  gcc_jit_rvalue *xtype = jit_compile_XTYPE (ctxt, o),
    *mask = gcc_jit_context_new_rvalue_from_int (ctxt->ctxt, int_type,
                                                 Lisp_Int0 | ~Lisp_Int1),
    *res,
    *int0 = gcc_jit_context_new_rvalue_from_int (ctxt->ctxt, int_type,
                                                 Lisp_Int0);
  xtype = jit_compile_cast_to (ctxt, xtype, int_type);
  res = gcc_jit_context_new_binary_op (ctxt->ctxt, NULL,
                                       GCC_JIT_BINARY_OP_BITWISE_AND, int_type,
                                       xtype, mask);
  return gcc_jit_context_new_comparison (ctxt->ctxt, NULL,
                                         GCC_JIT_COMPARISON_EQ, res,
                                         int0);
}

static gcc_jit_rvalue *
jit_compile_SYMBOLP (struct jit_context *ctxt, gcc_jit_rvalue *o)
{
  gcc_jit_type *typ = gcc_jit_context_get_type (ctxt->ctxt, GCC_JIT_TYPE_INT);
  gcc_jit_rvalue *v1 = gcc_jit_context_new_rvalue_from_int (ctxt->ctxt, typ,
                                                            Lisp_Symbol);
  return gcc_jit_context_new_comparison (ctxt->ctxt, NULL, GCC_JIT_COMPARISON_EQ,
                                         jit_compile_XTYPE (ctxt, o), v1);
}

static gcc_jit_rvalue *
jit_compile_FLOATP (struct jit_context *ctxt, gcc_jit_rvalue *o)
{
  gcc_jit_type *typ = gcc_jit_context_get_type (ctxt->ctxt, GCC_JIT_TYPE_INT);
  gcc_jit_rvalue *v1 = gcc_jit_context_new_rvalue_from_int (ctxt->ctxt, typ,
                                                            Lisp_Float);
  return gcc_jit_context_new_comparison (ctxt->ctxt, NULL, GCC_JIT_COMPARISON_EQ,
                                         jit_compile_XTYPE (ctxt, o), v1);
}

static gcc_jit_rvalue *
jit_compile_INTEGERP (struct jit_context *ctxt, gcc_jit_rvalue *o)
{
  gcc_jit_type *ptr_type =
    gcc_jit_context_new_function_ptr_type (ctxt->ctxt, NULL, ctxt->type_bool, 1,
                                           &(ctxt->type_lisp_object), 0);
  gcc_jit_rvalue *fixnump = jit_compile_FIXNUMP (ctxt, o),
    *fn_ptr = gcc_jit_context_new_rvalue_from_ptr (ctxt->ctxt, ptr_type,
                                                     BIGNUMP),
    *bignump = gcc_jit_context_new_call_through_ptr (ctxt->ctxt, NULL, fn_ptr,
                                                     1, &o);
  return gcc_jit_context_new_binary_op (ctxt->ctxt, NULL,
                                        GCC_JIT_BINARY_OP_LOGICAL_OR,
                                        ctxt->type_bool, fixnump, bignump);
}

static gcc_jit_rvalue *
jit_compile_NUMBERP (struct jit_context *ctxt, gcc_jit_rvalue *o)
{
  gcc_jit_rvalue *integerp = jit_compile_INTEGERP (ctxt, o),
    *floatp = jit_compile_FLOATP (ctxt, o);
  return gcc_jit_context_new_binary_op (ctxt->ctxt, NULL,
                                        GCC_JIT_BINARY_OP_LOGICAL_OR,
                                        ctxt->type_bool, integerp, floatp);
}

static gcc_jit_rvalue *
jit_compile_wrong_type_argument (struct jit_context *ctxt,
                                 Lisp_Object predicate, gcc_jit_rvalue *x)
{
  gcc_jit_type *args_types[2] = {ctxt->type_lisp_object, ctxt->type_lisp_object};
  gcc_jit_type *fn_ptr_type =
    gcc_jit_context_new_function_ptr_type (ctxt->ctxt, NULL, ctxt->type_void, 2,
                                           args_types, 0);
  gcc_jit_rvalue *fn_ptr =
    gcc_jit_context_new_rvalue_from_ptr (ctxt->ctxt, fn_ptr_type,
                                         wrong_type_argument);
  gcc_jit_rvalue *args[2] = {jit_new_rvalue_from_lisp_object(ctxt, predicate),
                             x};
  return gcc_jit_context_new_call_through_ptr (ctxt->ctxt, NULL, fn_ptr, 2,
                                               args);
}

static _Noreturn void
wrong_number_of_arguments (ptrdiff_t mandatory, ptrdiff_t nonrest,
                           ptrdiff_t nargs)
{
  Fsignal (Qwrong_number_of_arguments,
           list2 (Fcons (make_fixnum (mandatory), make_fixnum (nonrest)),
                  make_fixnum (nargs)));
}

static gcc_jit_rvalue *
jit_compile_arithcompare (struct jit_context *ctxt, gcc_jit_rvalue *a,
                            gcc_jit_rvalue *b, enum Arith_Comparison cmp)
{
  gcc_jit_type *int_type = gcc_jit_context_get_type (ctxt->ctxt,
                                                     GCC_JIT_TYPE_INT),
    *param_types[3] = {ctxt->type_lisp_object,
                       ctxt->type_lisp_object,
                       int_type},
    *ptr_type =
    gcc_jit_context_new_function_ptr_type (ctxt->ctxt, NULL,
                                           ctxt->type_lisp_object, 3,
                                           param_types, 0);
  gcc_jit_rvalue *args[3] = {a, b,
                             gcc_jit_context_new_rvalue_from_int (ctxt->ctxt,
                                                                  int_type,
                                                                  cmp)},
    *fn_ptr =
    gcc_jit_context_new_rvalue_from_ptr (ctxt->ctxt, ptr_type, arithcompare);

  return gcc_jit_context_new_call_through_ptr (ctxt->ctxt, NULL, fn_ptr, 3,
                                               args);
}


static gcc_jit_rvalue *
jit_compile_XCONS (struct jit_context *ctxt, gcc_jit_rvalue *o)
{
  return jit_compile_XUNTAG (ctxt, o, Lisp_Cons, ctxt->type_void_ptr);
}

static gcc_jit_rvalue *
jit_compile_XFIXNUM (struct jit_context *ctxt, gcc_jit_rvalue *o)
{
  gcc_jit_type *int_type = gcc_jit_context_get_type (ctxt->ctxt,
                                                     GCC_JIT_TYPE_INT);
  gcc_jit_rvalue *xli = jit_compile_XLI (ctxt, o, false),
    *inttypebits = gcc_jit_context_new_rvalue_from_int (ctxt->ctxt, int_type,
                                                        INTTYPEBITS);
  return gcc_jit_context_new_binary_op (ctxt->ctxt, NULL,
                                        GCC_JIT_BINARY_OP_RSHIFT,
                                        ctxt->type_emacs_int, xli, inttypebits);
}

static gcc_jit_rvalue *
jit_compile_XCAR (struct jit_context *ctxt, gcc_jit_rvalue *c)
{
  gcc_jit_type *char_ptr_type =
    gcc_jit_type_get_pointer (gcc_jit_context_get_type (ctxt->ctxt,
                                                        GCC_JIT_TYPE_CHAR)),
    *size_t_type = gcc_jit_context_get_type (ctxt->ctxt,
                                             GCC_JIT_TYPE_SIZE_T);

  gcc_jit_rvalue *offset =
    gcc_jit_context_new_rvalue_from_long (ctxt->ctxt, size_t_type,
                                          offsetof (struct Lisp_Cons, u.s.car)),
    *cons_ptr = jit_compile_cast_to (ctxt, jit_compile_XCONS (ctxt, c),
                                     char_ptr_type);
  gcc_jit_lvalue *field
    = gcc_jit_context_new_array_access (ctxt->ctxt, NULL, cons_ptr, offset);
  gcc_jit_rvalue *field_addr = gcc_jit_lvalue_get_address (field, NULL);
  gcc_jit_rvalue *car =
    jit_compile_cast_to (ctxt, field_addr,
                         gcc_jit_type_get_pointer (ctxt->type_lisp_object));

  return gcc_jit_lvalue_as_rvalue (gcc_jit_rvalue_dereference (car, NULL));
}

static gcc_jit_rvalue *
jit_compile_XCDR (struct jit_context *ctxt, gcc_jit_rvalue *c)
{
  gcc_jit_type *char_ptr_type =
    gcc_jit_type_get_pointer (gcc_jit_context_get_type (ctxt->ctxt,
                                                        GCC_JIT_TYPE_CHAR)),
    *size_t_type = gcc_jit_context_get_type (ctxt->ctxt,
                                             GCC_JIT_TYPE_SIZE_T);

  gcc_jit_rvalue *offset =
    gcc_jit_context_new_rvalue_from_long (ctxt->ctxt, size_t_type,
                                          offsetof (struct Lisp_Cons,
                                                    u.s.u.cdr)),
    *cons_ptr = jit_compile_cast_to (ctxt, jit_compile_XCONS (ctxt, c),
                                     char_ptr_type);
  gcc_jit_lvalue *field
    = gcc_jit_context_new_array_access (ctxt->ctxt, NULL, cons_ptr, offset);
  gcc_jit_rvalue *field_addr = gcc_jit_lvalue_get_address (field, NULL);
  gcc_jit_rvalue *cdr =
    jit_compile_cast_to (ctxt, field_addr,
                         gcc_jit_type_get_pointer (ctxt->type_lisp_object));
  return gcc_jit_lvalue_as_rvalue (gcc_jit_rvalue_dereference (cdr, NULL));
}

static gcc_jit_rvalue *
jit_compile_assume (struct jit_context *ctxt, gcc_jit_rvalue *a)
{
  gcc_jit_type *type_long = gcc_jit_context_get_type (ctxt->ctxt,
                                                      GCC_JIT_TYPE_LONG);
  a = gcc_jit_context_new_cast (ctxt->ctxt, NULL, a, type_long);
  gcc_jit_function *func =
    gcc_jit_context_get_builtin_function (ctxt->ctxt, "__builtin_expect");
  gcc_jit_rvalue *args[2] = {a, gcc_jit_context_one (ctxt->ctxt, type_long)};
  return gcc_jit_context_new_call (ctxt->ctxt, NULL, func, 2, args);
}

static gcc_jit_rvalue *
jit_compile_not (struct jit_context *ctxt, gcc_jit_rvalue *v)
{
  return gcc_jit_context_new_unary_op (ctxt->ctxt, NULL,
                                       GCC_JIT_UNARY_OP_LOGICAL_NEGATE,
                                       gcc_jit_context_get_type
                                       (ctxt->ctxt, GCC_JIT_TYPE_BOOL), v);
}

static gcc_jit_rvalue *
jit_compile_record_xmalloc (struct jit_context *ctxt, gcc_jit_type *type,
                            size_t size)
{
  gcc_jit_type *size_t_type = gcc_jit_context_get_type (ctxt->ctxt,
                                                        GCC_JIT_TYPE_SIZE_T);
  gcc_jit_type *ptr_type = gcc_jit_context_new_function_ptr_type (ctxt->ctxt,
                                                                  NULL, type,
                                                                  1,
                                                                  &size_t_type,
                                                                  0);
  gcc_jit_rvalue *fn_ptr = gcc_jit_context_new_rvalue_from_ptr (ctxt->ctxt,
                                                                ptr_type,
                                                                record_xmalloc),
    *arg =  gcc_jit_context_new_rvalue_from_long (ctxt->ctxt,
                                                  size_t_type,
                                                  size);
  return gcc_jit_context_new_call_through_ptr (ctxt->ctxt, NULL, fn_ptr, 1,
                                               &arg);

}

struct jit_context *
jit_new_context(void)
{
  struct jit_context *ctxt = xmalloc (sizeof (struct jit_context));

  ctxt->ctxt = gcc_jit_context_acquire();

  gcc_jit_context_set_bool_allow_unreachable_blocks (ctxt->ctxt, true);
  /* gcc_jit_context_set_bool_option (ctxt->ctxt, */
  /*                                  GCC_JIT_BOOL_OPTION_DUMP_SUMMARY, true); */
  /* gcc_jit_context_set_bool_option (ctxt->ctxt, */
  /*                                  GCC_JIT_BOOL_OPTION_DUMP_EVERYTHING, true); */
  gcc_jit_context_set_bool_option (ctxt->ctxt, GCC_JIT_BOOL_OPTION_DEBUGINFO,
                                   true);
  ctxt->type_emacs_int = gcc_jit_context_get_type (ctxt->ctxt,
                                                   JIT_TYPE_EMACS_INT);
  ctxt->type_emacs_uint = gcc_jit_context_get_type (ctxt->ctxt,
                                                    JIT_TYPE_EMACS_UINT);

  if (LISP_WORDS_ARE_POINTERS)
    ctxt->type_lisp_word = gcc_jit_context_get_type (ctxt->ctxt,
                                                     GCC_JIT_TYPE_VOID_PTR);
  else
    ctxt->type_lisp_word = ctxt->type_emacs_int;

  if (CHECK_LISP_OBJECT_TYPE)
    {
      ctxt->field_lisp_object = gcc_jit_context_new_field (ctxt->ctxt, NULL,
                                                           ctxt->type_lisp_word,
                                                           "i");
      ctxt->struct_lisp_object =
        gcc_jit_context_new_struct_type (ctxt->ctxt, NULL, "Lisp_Object",
                                         1, &ctxt->field_lisp_object);
      ctxt->type_lisp_object = gcc_jit_struct_as_type (ctxt->struct_lisp_object);
    }
  else
    ctxt->type_lisp_object = ctxt->type_lisp_word;

  ctxt->type_lisp_type = gcc_jit_context_get_type (ctxt->ctxt,
                                                   GCC_JIT_TYPE_INT);
  if (!CHECK_LISP_OBJECT_TYPE)
    {
      ctxt->rvalue_nil = jit_new_rvalue_from_lisp_object (ctxt, Qnil);
      ctxt->rvalue_t = jit_new_rvalue_from_lisp_object (ctxt, Qt);
    }

  ctxt->local_index = 0;
  ctxt->type_intptr_t = gcc_jit_context_get_int_type (ctxt->ctxt,
                                                      sizeof (intptr_t), 1);
  ctxt->type_char_ptr =
    gcc_jit_type_get_pointer (gcc_jit_context_get_type (ctxt->ctxt,
                                                        GCC_JIT_TYPE_CHAR)),
  ctxt->type_void_ptr = gcc_jit_context_get_type (ctxt->ctxt,
                                                  GCC_JIT_TYPE_VOID_PTR);
  ctxt->type_void = gcc_jit_context_get_type (ctxt->ctxt,
                                              GCC_JIT_TYPE_VOID);
  ctxt->type_ptrdiff_t = gcc_jit_context_get_int_type (ctxt->ctxt,
                                                       sizeof(ptrdiff_t),
                                                       1);
  ctxt->type_bool = gcc_jit_context_get_type (ctxt->ctxt, GCC_JIT_TYPE_BOOL);
  return ctxt;
}

static Lisp_Object
native_current_column (void)
{
  return make_fixed_natnum (current_column ());
}

static Lisp_Object
native_point (void)
{
  return make_fixed_natnum (PT);
}

static Lisp_Object
native_char_syntax (Lisp_Object o)
{
  CHECK_CHARACTER (o);
  int c = XFIXNAT (o);
  if (NILP (BVAR (current_buffer, enable_multibyte_characters)))
    MAKE_CHAR_MULTIBYTE (c);
  XSETFASTINT (o, syntax_code_spec[SYNTAX (c)]);
  return Qnil;
}

#ifndef isnan
# define isnan(x) ((x) != (x))
#endif

static Lisp_Object
minmax_driver_2 (Lisp_Object o1, Lisp_Object o2,
                 enum Arith_Comparison comparison)
{
  Lisp_Object accum = o1;
  CHECK_NUMBER_COERCE_MARKER (accum);

  CHECK_NUMBER_COERCE_MARKER (o2);
  if (!NILP (arithcompare (o2, accum, comparison)))
    accum = o2;
  else if (FLOATP (o2) && isnan (XFLOAT_DATA (o2)))
    return o2;

  return accum;
}

static gcc_jit_rvalue *
jit_compile_minmax_driver (struct jit_context *ctxt, enum Arith_Comparison code,
                           gcc_jit_rvalue *v1, gcc_jit_rvalue *v2)
{
  gcc_jit_type *int_type = gcc_jit_context_get_type (ctxt->ctxt,
                                                     GCC_JIT_TYPE_INT),
    *args_types[3] = {ctxt->type_lisp_object, ctxt->type_lisp_object, int_type},
    *ptr_type =
    gcc_jit_context_new_function_ptr_type (ctxt->ctxt, NULL,
                                           ctxt->type_lisp_object, 3,
                                           args_types, 0);
  gcc_jit_rvalue *fn_ptr =
    gcc_jit_context_new_rvalue_from_ptr (ctxt->ctxt, ptr_type,
                                         minmax_driver_2),
    *code_r = gcc_jit_context_new_rvalue_from_int (ctxt->ctxt, int_type, code);
  gcc_jit_rvalue *args[3] = {v1, v2, code_r};
  gcc_jit_rvalue *call = gcc_jit_context_new_call_through_ptr (ctxt->ctxt, NULL,
                                                               fn_ptr, 3,
                                                               args);
  return call;
}

static void
native_varset (Lisp_Object sym, Lisp_Object val)
{
  if (SYMBOLP (sym)
      && !EQ (val, Qunbound)
      && !XSYMBOL (sym)->u.s.redirect
      && !SYMBOL_TRAPPED_WRITE_P (sym))
    SET_SYMBOL_VAL (XSYMBOL (sym), val);
  else
    set_internal (sym, val, Qnil, SET_INTERNAL_SET);
}

static gcc_jit_rvalue *
jit_get_main_thread (struct jit_context *ctxt)
{
  return gcc_jit_context_new_rvalue_from_ptr (ctxt->ctxt, ctxt->type_void_ptr,
                                              current_thread);
}

static gcc_jit_rvalue *
jit_compile_struct_deref (struct jit_context *ctxt, gcc_jit_rvalue *struct_r,
                          size_t offset, gcc_jit_type *cast_to)
{
  gcc_jit_type *size_t_type = gcc_jit_context_get_type (ctxt->ctxt,
                                                        GCC_JIT_TYPE_SIZE_T),
    *cast_to_ptr = gcc_jit_type_get_pointer (cast_to);
  gcc_jit_rvalue *struct_cast = jit_compile_cast_to (ctxt, struct_r,
                                                     ctxt->type_char_ptr),
    *index = gcc_jit_context_new_rvalue_from_int (ctxt->ctxt, size_t_type,
                                                  offset);
  gcc_jit_lvalue *field = gcc_jit_context_new_array_access (ctxt->ctxt, NULL,
                                                            struct_cast, index);
  gcc_jit_rvalue *field_addr =
    jit_compile_cast_to (ctxt, gcc_jit_lvalue_get_address (field, NULL),
                         cast_to_ptr);
  return gcc_jit_lvalue_as_rvalue (gcc_jit_rvalue_dereference (field_addr,
                                                               NULL));
}

static gcc_jit_rvalue *
jit_new_rvalue_from_intptr (struct jit_context *ctxt, intptr_t i)
{
  if (sizeof (intptr_t) == sizeof (int) ||
      sizeof (intptr_t) == sizeof (short int))
    return gcc_jit_context_new_rvalue_from_int (ctxt->ctxt, ctxt->type_intptr_t,
                                                i);
  return gcc_jit_context_new_rvalue_from_long (ctxt->ctxt, ctxt->type_intptr_t,
                                               i);
}

static gcc_jit_rvalue *
jit_compile_SPECDCL_INDEX (struct jit_context *ctxt)
{
  gcc_jit_rvalue *ptr =
    jit_compile_struct_deref (ctxt, jit_get_main_thread (ctxt),
                              offsetof (struct thread_state, m_specpdl_ptr),
                              ctxt->type_intptr_t),
    *pdl = jit_compile_struct_deref (ctxt, jit_get_main_thread (ctxt),
                                     offsetof (struct thread_state, m_specpdl),
                                     ctxt->type_intptr_t),
    *diff = gcc_jit_context_new_binary_op (ctxt->ctxt, NULL,
                                           GCC_JIT_BINARY_OP_MINUS,
                                           ctxt->type_intptr_t,
                                           ptr, pdl),
    *size = jit_new_rvalue_from_intptr (ctxt, sizeof (union specbinding)),
    *index = gcc_jit_context_new_binary_op (ctxt->ctxt, NULL,
                                            GCC_JIT_BINARY_OP_DIVIDE,
                                            ctxt->type_intptr_t,
                                            diff, size);
  return gcc_jit_context_new_cast (ctxt->ctxt, NULL, index,
                                   ctxt->type_ptrdiff_t);
}

static void
jit_compile_unbind_to (struct jit_context *ctxt, gcc_jit_rvalue *count,
                       gcc_jit_rvalue *value)
{
  gcc_jit_type *args_types[2] = {ctxt->type_ptrdiff_t, ctxt->type_lisp_object},
    *ptr_type =
    gcc_jit_context_new_function_ptr_type (ctxt->ctxt, NULL,
                                           ctxt->type_lisp_object, 2,
                                           args_types, 0);
  gcc_jit_rvalue *fn_ptr =
    gcc_jit_context_new_rvalue_from_ptr (ctxt->ctxt, ptr_type,
                                         unbind_to),
    *args[2] = {count, value},
    *call = gcc_jit_context_new_call_through_ptr (ctxt->ctxt, NULL, fn_ptr, 2,
                                                  args);
  gcc_jit_block_add_eval (ctxt->cur_block, NULL, call);
}

static gcc_jit_rvalue *
jit_compile_record_unwind_protect_rvalue (struct jit_context *ctxt,
                                          gcc_jit_rvalue *call_fn_ptr,
                                          gcc_jit_rvalue *arg)
{
  gcc_jit_type *args_types[2] = {ctxt->type_void_ptr,
                                 ctxt->type_lisp_object};
  gcc_jit_type *fn_type =
    gcc_jit_context_new_function_ptr_type (ctxt->ctxt, NULL,
                                           ctxt->type_void, 2,
                                           args_types, 0);
  gcc_jit_rvalue *fn_ptr =
    gcc_jit_context_new_rvalue_from_ptr (ctxt->ctxt, fn_type,
                                         record_unwind_protect);
  gcc_jit_rvalue *args[2] = {call_fn_ptr, arg};
  return gcc_jit_context_new_call_through_ptr (ctxt->ctxt, NULL, fn_ptr, 2,
                                               args);
}

static gcc_jit_rvalue *
jit_compile_record_unwind_protect (struct jit_context *ctxt,
                                   void (*function) (Lisp_Object),
                                   Lisp_Object arg)
{
  gcc_jit_rvalue *fn_ptr =
    gcc_jit_context_new_rvalue_from_ptr (ctxt->ctxt, ctxt->type_void_ptr,
                                         function);
  gcc_jit_rvalue *arg_rvalue = jit_new_rvalue_from_lisp_object (ctxt, arg);
  return jit_compile_record_unwind_protect_rvalue (ctxt, fn_ptr, arg_rvalue);
}

static void
check_count (ptrdiff_t init_count, ptrdiff_t final_count)
{
  if (init_count != final_count)
    {
      if (final_count > init_count)
        unbind_to (init_count, Qnil);
      error ("binding stack not balanced (serious byte/jit compiler bug)");
    }
}

static void
jit_compile_return (struct jit_context *ctxt, gcc_jit_rvalue *init_count,
                    gcc_jit_rvalue *val)
{
  gcc_jit_rvalue *final_count = jit_compile_SPECDCL_INDEX (ctxt);
  gcc_jit_type *param_types[2] = {ctxt->type_ptrdiff_t, ctxt->type_ptrdiff_t},
    *ptr_type_check = gcc_jit_context_new_function_ptr_type (ctxt->ctxt, NULL,
                                                             ctxt->type_void, 2,
                                                             param_types, 0);
  gcc_jit_rvalue *fn_ptr_check =
    gcc_jit_context_new_rvalue_from_ptr (ctxt->ctxt,
                                         ptr_type_check,
                                         check_count),
    *args_check[2] = {init_count, final_count},
    *call_check = gcc_jit_context_new_call_through_ptr (ctxt->ctxt, NULL,
                                                        fn_ptr_check, 2,
                                                        args_check);
  gcc_jit_block_add_comment (ctxt->cur_block, NULL,
                             "check_count (init_count, SPECPDL_INDEX ())");
  gcc_jit_block_add_eval (ctxt->cur_block, NULL, call_check);
  gcc_jit_block_end_with_return (ctxt->cur_block, NULL, val);
}

static void
jit_compile (struct jit_context *ctxt, Lisp_Object func, char *func_name,
             Lisp_Object file_dump_name, Lisp_Object dot_dump_name,
             Lisp_Object assembly_name, Lisp_Object opt_level,
             struct jit_result *result, Lisp_Object *error,
             Lisp_Object *error_data)
{
  USE_SAFE_ALLOCA;
  ctxt->local_index = 0;
  if (ctxt->block_stack != NULL)
    {
      jit_block_stack_free (ctxt->block_stack);
      ctxt->block_stack = NULL;
    }

  Lisp_Object arglist = AREF (func, COMPILED_ARGLIST);
  Lisp_Object bytestr = AREF(func, COMPILED_BYTECODE);
  CHECK_STRING (bytestr);

  if (STRING_MULTIBYTE (bytestr))
    bytestr = Fstring_as_unibyte (bytestr);

  Lisp_Object vector = AREF (func, COMPILED_CONSTANTS);
  CHECK_VECTOR (vector);
  ptrdiff_t vector_size = ASIZE (vector);
  Lisp_Object *vectorp = XVECTOR (vector)->contents;

  Lisp_Object maxdepth = AREF (func, COMPILED_STACK_DEPTH);
  CHECK_FIXNAT (maxdepth);

  unsigned char *bytestr_data = SDATA (bytestr);
  ptrdiff_t bytestr_length = SBYTES (bytestr);
  unsigned char const *pc = bytestr_data;

  int stack_top = -1, i;
  gcc_jit_lvalue **var_stack = SAFE_ALLOCA (sizeof (gcc_jit_lvalue *)
                                            * XFIXNAT (maxdepth));
  gcc_jit_block *prev_block = NULL;
  /* gcc_jit_context_set_logfile (ctxt->ctxt, stderr, 0, 0); */
  if (!NILP (opt_level))
    {
      CHECK_INTEGER (opt_level);
      if (XFIXNUM (opt_level) < 0 || XFIXNUM (opt_level) > 3)
        {
          *error = Qjit_invalid_optimization_level;
          *error_data = list1(opt_level);
          return;
        }
      gcc_jit_context_set_int_option (ctxt->ctxt,
                                      GCC_JIT_INT_OPTION_OPTIMIZATION_LEVEL,
                                      XFIXNUM (opt_level));
    }

  bool set_prev_block_null = false;
  ptrdiff_t func_params_num = 0;
  gcc_jit_param **params = NULL;

  result->min_args = 0;
  result->max_args = 0;
  gcc_jit_type *lo_ptr_type = gcc_jit_type_get_pointer (ctxt->type_lisp_object);
  gcc_jit_type *int_type = gcc_jit_context_get_type (ctxt->ctxt,
                                                     GCC_JIT_TYPE_INT);

  if (FIXNUMP (arglist))
    {
      ptrdiff_t at = XFIXNUM (arglist);
      if ((at & 128) !=0)
        emacs_abort();
      ptrdiff_t nonrest = at >> 8;
      ptrdiff_t mandatory = at & 127;

      result->min_args = mandatory;
      result->max_args = nonrest;

      func_params_num = 2;
      params = SAFE_ALLOCA (sizeof (gcc_jit_param *) * func_params_num);
      params[0] = gcc_jit_context_new_param (ctxt->ctxt, NULL,
                                             ctxt->type_lisp_object, "n");
      params[1] = gcc_jit_context_new_param (ctxt->ctxt, NULL, lo_ptr_type,
                                             "args");
    }

  ctxt->cur_func = gcc_jit_context_new_function (ctxt->ctxt, NULL,
                                                 GCC_JIT_FUNCTION_EXPORTED,
                                                 ctxt->type_lisp_object,
                                                 func_name, func_params_num,
                                                 params, 0);
  gcc_jit_block *scratch_alloc_block =
    gcc_jit_function_new_block (ctxt->cur_func, NULL);
  gcc_jit_lvalue *scratch_local = gcc_jit_function_new_local (ctxt->cur_func,
                                                              NULL, lo_ptr_type,
                                                              "scratch");
  gcc_jit_rvalue *scratch = gcc_jit_lvalue_as_rvalue (scratch_local);
  ptrdiff_t scratch_max_args = 0;

  gcc_jit_block *first_block = ctxt->cur_block =
    gcc_jit_function_new_block (ctxt->cur_func, NULL);
  if (CHECK_LISP_OBJECT_TYPE)
    {
      ctxt->rvalue_nil = jit_new_rvalue_from_lisp_object (ctxt, Qnil);
      ctxt->rvalue_t = jit_new_rvalue_from_lisp_object (ctxt, Qt);
    }
  gcc_jit_lvalue *init_count =
    gcc_jit_function_new_local (ctxt->cur_func, NULL, ctxt->type_ptrdiff_t,
                                "init_count");

  JIT_ADD_COMMENT ("init_count = SPECDCL_INDEX ();");
  gcc_jit_block_add_assignment (ctxt->cur_block, NULL,
                                init_count,
                                jit_compile_SPECDCL_INDEX (ctxt));
  for (i = 0; i < XFIXNAT (maxdepth); i++)
    {
      var_stack[i] = jit_new_local (ctxt, ctxt->type_lisp_object);
      if (FIXNUMP (arglist) && i < result->max_args)
        {
          stack_top++;
          gcc_jit_rvalue *index =
            gcc_jit_context_new_rvalue_from_int (ctxt->ctxt, int_type, i);
          gcc_jit_lvalue *val =
            gcc_jit_context_new_array_access (ctxt->ctxt,
                                              NULL,
                                              gcc_jit_param_as_rvalue (params[1]),
                                              index);
          gcc_jit_block_add_assignment (ctxt->cur_block, NULL, var_stack[i],
                                        gcc_jit_lvalue_as_rvalue (val));
        }
      else
        gcc_jit_block_add_assignment (ctxt->cur_block, NULL, var_stack[i],
                                      ctxt->rvalue_nil);
    }

  struct jit_block_stack *block_stack = jit_block_stack_new ();
  ctxt->block_stack = block_stack;

  while (pc < bytestr_data + bytestr_length)
    {
      if (stack_top < -1 || stack_top >= XFIXNAT (maxdepth))
        {
          *error = stack_top < -1 ? Qjit_stack_underflow : Qjit_stack_overflow;
          *error_data = list1(make_fixnum (stack_top));
          return;
        }
      int op = FETCH;
      char buf[80];

      switch (op)
        {
        case Bvarref7:
        case Bvarref:
        case Bvarref1:
        case Bvarref2:
        case Bvarref3:
        case Bvarref4:
        case Bvarref5:
          op -= Bvarref;
          goto varref;
        case Bvarref6:
          op = FETCH;
        varref:
          {
            gcc_jit_rvalue *v1 = jit_new_rvalue_from_lisp_object (ctxt,
                                                                  vectorp[op]);
            gcc_jit_rvalue *val =
              jit_compile_call_to_subr (ctxt, Fsymbol_value, 1, v1);
            JIT_ADD_COMMENT (SSDATA (CALLN (Fformat_message,
                                           build_string
                                           ("PUSH (Fsymbol_value (%s))"),
                                           vectorp[op])));
            gcc_jit_block_add_assignment (ctxt->cur_block, NULL,
                                          var_stack[++stack_top],
                                          val);
            break;
          }

        case Bcar:
          {
            gcc_jit_lvalue *top = var_stack[stack_top];

            gcc_jit_rvalue *v1_rvalue = gcc_jit_lvalue_as_rvalue (top);
            gcc_jit_block *final_block =
              gcc_jit_function_new_block (ctxt->cur_func, "next"),
              *consp_block =
              gcc_jit_function_new_block (ctxt->cur_func, "consp"),
              *not_consp_block = gcc_jit_function_new_block (ctxt->cur_func,
                                                             "not_consp"),
              *old_block = ctxt->cur_block;

            gcc_jit_rvalue *is_consp = jit_compile_CONSP (ctxt, v1_rvalue);

            /* if CONSP(v1) goto consp_block else goto not_consp_block; */
            gcc_jit_block_end_with_conditional (ctxt->cur_block, NULL, is_consp,
                                                consp_block, not_consp_block);

            { /* consp_block: */
              ctxt->cur_block = consp_block;
              JIT_ADD_COMMENT_BLOCK (consp_block, "top = XCAR (top)");
              gcc_jit_block_add_assignment (consp_block, NULL,
                                            top,
                                            jit_compile_XCAR (ctxt, v1_rvalue));
              /* goto final_block */
              gcc_jit_block_end_with_jump (consp_block, NULL, final_block);
            }
            { /* not_consp_block: */
              ctxt->cur_block = not_consp_block;
              gcc_jit_rvalue *is_not_nilp = jit_compile_not_NILP (ctxt, v1_rvalue);
              gcc_jit_block *not_nilp_block =
                gcc_jit_function_new_block (ctxt->cur_func, "is_not_nilp");
              /* if !NILP(v1) goto is_not_nilp else goto final_block */
              gcc_jit_block_end_with_conditional (not_consp_block, NULL,
                                                  is_not_nilp, not_nilp_block,
                                                  final_block);
              { /* is_not_nilp: */
                ctxt->cur_block = not_nilp_block;
                JIT_ADD_COMMENT ("wrong_type_argument (Qlistp, TOP)");
                gcc_jit_rvalue *wrong_arg =
                  jit_compile_wrong_type_argument (ctxt, Qlistp, v1_rvalue);
                gcc_jit_block_add_eval (not_nilp_block, NULL, wrong_arg);
                jit_compile_block_unreachable (ctxt, not_nilp_block);
                /* goto final_block */
                gcc_jit_block_end_with_jump (not_nilp_block, NULL, final_block);
              }
            }

            if (prev_block)
              gcc_jit_block_end_with_jump (prev_block, NULL, old_block);

            prev_block = NULL;
            ctxt->cur_block = final_block;
            break;
          }
        case Beq:
          {
            gcc_jit_lvalue *v1 = var_stack[stack_top--],
              *v2 = var_stack[stack_top];
            gcc_jit_rvalue *eql = jit_compile_EQ (ctxt,
                                                  gcc_jit_lvalue_as_rvalue (v1),
                                                  gcc_jit_lvalue_as_rvalue (v2));
            gcc_jit_block *old_block = ctxt->cur_block;

            JIT_ADD_COMMENT ("v2 = EQ (v1, v2);");
            jit_compile_assign_ternary (ctxt, eql, v2, ctxt->rvalue_t,
                                        ctxt->rvalue_nil, &ctxt->cur_block);

            if (prev_block)
              gcc_jit_block_end_with_jump (prev_block, NULL, old_block);

            prev_block = NULL;
            break;
          }
        case Bmemq:
          {
            gcc_jit_lvalue *v1 = var_stack[stack_top--],
              *top = var_stack[stack_top];
            gcc_jit_rvalue *call =
              jit_compile_call_to_subr (ctxt, Fmemq, 2,
                                        gcc_jit_lvalue_as_rvalue (top),
                                        gcc_jit_lvalue_as_rvalue (v1));
            JIT_ADD_COMMENT("v1 = POP; TOP = Fmemq (v1, TOP)");
            gcc_jit_block_add_assignment (ctxt->cur_block, NULL, top, call);
            break;
          }
        case Bcdr:
          {
            gcc_jit_lvalue *v1 = var_stack[stack_top];
            gcc_jit_rvalue *v1_rvalue = gcc_jit_lvalue_as_rvalue(v1);
            gcc_jit_block *final_block =
              gcc_jit_function_new_block (ctxt->cur_func, "next"),
              *consp_block = gcc_jit_function_new_block (ctxt->cur_func,
                                                         "CONSP(o)"),
              *not_consp_block = gcc_jit_function_new_block (ctxt->cur_func,
                                                             "!CONSP(o)"),
              *old_block = ctxt->cur_block;
            gcc_jit_rvalue *is_consp = jit_compile_CONSP (ctxt, v1_rvalue);

            /* if CONSP(v1) goto consp_block else goto not_consp_block; */
            gcc_jit_block_end_with_conditional (ctxt->cur_block, NULL, is_consp,
                                                consp_block, not_consp_block);

            { /* consp_block: */
              ctxt->cur_block = consp_block;
              JIT_ADD_COMMENT ("top = XCDR (top)");
              gcc_jit_block_add_assignment (consp_block, NULL,
                                            v1,
                                            jit_compile_XCDR (ctxt, v1_rvalue));
              /* goto final_block */
              gcc_jit_block_end_with_jump (consp_block, NULL, final_block);
            }
            { /* not_consp_block: */
              ctxt->cur_block = not_consp_block;
              gcc_jit_rvalue *is_not_nilp = jit_compile_not_NILP (ctxt,
                                                                  v1_rvalue);
              gcc_jit_block *not_nilp_block =
                gcc_jit_function_new_block (ctxt->cur_func, "not_nilp");
              /* if !NILP(v1) goto is_not_nilp else goto final_block */
              gcc_jit_block_end_with_conditional (not_consp_block, NULL,
                                                  is_not_nilp, not_nilp_block,
                                                  final_block);
              { /* is_not_nilp: */
                ctxt->cur_block = not_nilp_block;
                JIT_ADD_COMMENT ("wrong_type_argument (Qlistp, TOP)");
                gcc_jit_rvalue *wrong_arg =
                  jit_compile_wrong_type_argument (ctxt, Qlistp, v1_rvalue);
                gcc_jit_block_add_eval (not_nilp_block, NULL, wrong_arg);
                jit_compile_block_unreachable (ctxt, not_nilp_block);
                /* goto final_block */
                gcc_jit_block_end_with_jump (not_nilp_block, NULL, final_block);
              }
            }

            if (prev_block)
              gcc_jit_block_end_with_jump(prev_block, NULL, old_block);

            prev_block = NULL;
            ctxt->cur_block = final_block;
            break;
          }

        case Bvarset:
        case Bvarset1:
        case Bvarset2:
        case Bvarset3:
        case Bvarset4:
        case Bvarset5:
          op -= Bvarset;
          goto varset;

        case Bvarset7:
          op = FETCH2;
          goto varset;

        case Bvarset6:
          op = FETCH;
        varset:
          {
            gcc_jit_rvalue *sym = jit_new_rvalue_from_lisp_object (ctxt,
                                                                   vectorp[op]);
            gcc_jit_lvalue *val = var_stack[stack_top--];
            gcc_jit_type *args[2] = {ctxt->type_lisp_object,
                                     ctxt->type_lisp_object},
              *void_ptr = gcc_jit_context_get_type (ctxt->ctxt,
                                                    GCC_JIT_TYPE_VOID),
              *fn_ptr =
              gcc_jit_context_new_function_ptr_type (ctxt->ctxt, NULL,
                                                     void_ptr, 2, args, 0);
            gcc_jit_rvalue *args_rvalue[2] = {sym,
                                              gcc_jit_lvalue_as_rvalue (val)},
              *func =
              gcc_jit_context_new_rvalue_from_ptr (ctxt->ctxt, fn_ptr,
                                                   native_varset);
            JIT_ADD_COMMENT (SSDATA (CALLN (Fformat_message,
                                           build_string
                                           ("PUSH (native_varset (%s))"),
                                           vectorp[op])));
            gcc_jit_rvalue *call =
              gcc_jit_context_new_call_through_ptr (ctxt->ctxt, NULL, func, 2,
                                                    args_rvalue);
            gcc_jit_block_add_eval (ctxt->cur_block, NULL, call);
            break;
          }
        case Bdup:
          {
            gcc_jit_lvalue *top = var_stack[stack_top],
              *v1 = var_stack[++stack_top];
            JIT_ADD_COMMENT ("v1 = TOP; PUSH (v1)");
            gcc_jit_block_add_assignment(ctxt->cur_block, NULL,
                                         v1,
                                         gcc_jit_lvalue_as_rvalue (top));
            break;
          }

        case Bvarbind6:
          op = FETCH;
          goto varbind;

        case Bvarbind7:
          op = FETCH2;
          goto varbind;

        case Bvarbind:
        case Bvarbind1:
        case Bvarbind2:
        case Bvarbind3:
        case Bvarbind4:
        case Bvarbind5:
          op -= Bvarbind;
        varbind:
          {
            gcc_jit_rvalue *sym = jit_new_rvalue_from_lisp_object (ctxt,
                                                                   vectorp[op]);
            gcc_jit_lvalue *val = var_stack[stack_top--];
            gcc_jit_type *args[2] = {ctxt->type_lisp_object,
                                     ctxt->type_lisp_object},
              *void_ptr = gcc_jit_context_get_type (ctxt->ctxt, GCC_JIT_TYPE_VOID);
            gcc_jit_type *fn_ptr =
              gcc_jit_context_new_function_ptr_type (ctxt->ctxt, NULL,
                                                     void_ptr, 2, args, 0);
            gcc_jit_rvalue *args_rvalue[2] = {sym,
                                              gcc_jit_lvalue_as_rvalue(val)};
            gcc_jit_rvalue *func =
              gcc_jit_context_new_rvalue_from_ptr (ctxt->ctxt, fn_ptr,
                                                   specbind);
            JIT_ADD_COMMENT (SSDATA (CALLN (Fformat_message,
                                           build_string
                                           ("specbind (%s, POP)"),
                                           vectorp[op])));
            gcc_jit_rvalue *call =
              gcc_jit_context_new_call_through_ptr (ctxt->ctxt, NULL, func, 2,
                                                    args_rvalue);
            gcc_jit_block_add_eval (ctxt->cur_block, NULL, call);
            break;
          }

        case Bcall6:
          op = FETCH;
          goto docall;

        case Bcall7:
          op = FETCH2;
          goto docall;

        case Bcall:
        case Bcall1:
        case Bcall2:
        case Bcall3:
        case Bcall4:
        case Bcall5:
          op -= Bcall;
        docall:
          {
            scratch_max_args = max (scratch_max_args, op + 1);
            gcc_jit_rvalue *call = jit_compile_call_to_many_subr (ctxt, op + 1,
                                                                  var_stack,
                                                                  stack_top,
                                                                  scratch,
                                                                  Ffuncall);
            stack_top -= op;
            gcc_jit_lvalue *top = var_stack[stack_top];
            sprintf (buf, "top = Ffuncall (%d, args...)", op + 1);
            gcc_jit_block_add_comment (ctxt->cur_block, NULL, buf);
            gcc_jit_block_add_assignment (ctxt->cur_block, NULL, top, call);
            break;
          }

        case Bunbind6:
          op = FETCH;
          goto dounbind;
        case Bunbind7:
          goto dounbind;
        case Bunbind:
        case Bunbind1:
        case Bunbind2:
        case Bunbind3:
        case Bunbind4:
        case Bunbind5:
          op -= Bunbind;
        dounbind:
          {
            gcc_jit_rvalue *count = jit_compile_SPECDCL_INDEX (ctxt);
            gcc_jit_rvalue *op_rvalue =
              jit_new_rvalue_from_ptrdiff_t (ctxt, (ptrdiff_t)op);
            count = gcc_jit_context_new_binary_op (ctxt->ctxt, NULL,
                                                   GCC_JIT_BINARY_OP_MINUS,
                                                   ctxt->type_ptrdiff_t, count,
                                                   op_rvalue);
            gcc_jit_rvalue *val = jit_new_rvalue_from_lisp_object (ctxt, Qnil);
            sprintf (buf, "unbind_to (SPECPDL_INDEX () - %d, Qnil)", op);
            gcc_jit_block_add_comment (ctxt->cur_block, NULL, buf);
            jit_compile_unbind_to (ctxt, count, val);
            break;
          }

        case Bunbind_all:
          JIT_ADD_COMMENT ("unbind_to (init_count, Qnil)");
          jit_compile_unbind_to (ctxt,
                                 gcc_jit_lvalue_as_rvalue (init_count),
                                 jit_new_rvalue_from_lisp_object (ctxt, Qnil));
          break;
        case Breturn:
          {
            gcc_jit_rvalue *return_val =
              (stack_top == -1) ? ctxt->rvalue_nil :
              gcc_jit_lvalue_as_rvalue (var_stack[stack_top]);

            if (prev_block)
              gcc_jit_block_end_with_jump (prev_block, NULL, ctxt->cur_block);

            prev_block = NULL;
            jit_compile_return (ctxt, gcc_jit_lvalue_as_rvalue(init_count),
                                return_val);
            break;
          }

        case Bdiscard:
          JIT_ADD_COMMENT ("discard");
          stack_top--;
          break;

        case Bsave_excursion:
          {
            gcc_jit_type *fn_ptr_type =
              gcc_jit_context_new_function_ptr_type (ctxt->ctxt, NULL,
                                                     ctxt->type_void, 0, NULL, 0);
            gcc_jit_rvalue *fn_ptr =
              gcc_jit_context_new_rvalue_from_ptr (ctxt->ctxt, fn_ptr_type,
                                                   record_unwind_protect_excursion);
            gcc_jit_rvalue *call =
              gcc_jit_context_new_call_through_ptr (ctxt->ctxt, NULL, fn_ptr, 0,
                                                    NULL);
            gcc_jit_block_add_eval (ctxt->cur_block, NULL, call);
            break;
          }
        case Bsave_current_buffer:
        case Bsave_current_buffer_1:
          {
            gcc_jit_type *fn_ptr_type =
              gcc_jit_context_new_function_ptr_type (ctxt->ctxt, NULL,
                                                     ctxt->type_void, 0, NULL, 0);
            gcc_jit_rvalue *fn_ptr =
              gcc_jit_context_new_rvalue_from_ptr (ctxt->ctxt, fn_ptr_type,
                                                   record_unwind_current_buffer);
            gcc_jit_rvalue *call =
              gcc_jit_context_new_call_through_ptr (ctxt->ctxt, NULL, fn_ptr, 0,
                                                    NULL);
            gcc_jit_block_add_eval (ctxt->cur_block, NULL, call);
            break;
          }
        case Bsave_restriction:
          {
            gcc_jit_type *fn_type =
              gcc_jit_context_new_function_ptr_type (ctxt->ctxt, NULL,
                                                     ctxt->type_lisp_object, 0,
                                                     NULL, 0);
            gcc_jit_rvalue *fn_ptr =
              gcc_jit_context_new_rvalue_from_ptr(ctxt->ctxt, fn_type,
                                                  save_restriction_save);
            gcc_jit_rvalue *arg =
              gcc_jit_context_new_call_through_ptr (ctxt->ctxt, NULL, fn_ptr, 0,
                                                    NULL);
            gcc_jit_rvalue *call =
              jit_compile_record_unwind_protect_rvalue (ctxt, fn_ptr, arg);
            gcc_jit_block_add_eval (ctxt->cur_block, NULL, call);
            break;
          }
        case Bcatch:
          {
            gcc_jit_lvalue *v1 = var_stack[stack_top--],
              *top = var_stack[stack_top];
            gcc_jit_type *param_types[3] = {ctxt->type_lisp_object,
                                            ctxt->type_void_ptr,
                                            ctxt->type_lisp_object},
              *ptr_type =
              gcc_jit_context_new_function_ptr_type (ctxt->ctxt, NULL,
                                                     ctxt->type_lisp_object, 3,
                                                     param_types, 0);
            gcc_jit_rvalue *fn_ptr =
              gcc_jit_context_new_rvalue_from_ptr (ctxt->ctxt, ptr_type,
                                                   internal_catch),
              *eval_sub_ptr =
              gcc_jit_context_new_rvalue_from_ptr (ctxt->ctxt,
                                                   ctxt->type_void_ptr,
                                                   eval_sub),
              *args[3] = {gcc_jit_lvalue_as_rvalue (top),
                          eval_sub_ptr,
                          gcc_jit_lvalue_as_rvalue (v1)},
              *call = gcc_jit_context_new_call_through_ptr (ctxt->ctxt,
                                                            NULL, fn_ptr, 3,
                                                            args);
            gcc_jit_block_add_assignment (ctxt->cur_block, NULL, top, call);
            break;
          }

        case Bunwind_protect:
          {
            gcc_jit_rvalue *handler =
              gcc_jit_lvalue_as_rvalue (var_stack[stack_top]),
              *functionp = jit_compile_FUNCTIONP (ctxt, handler);
            gcc_jit_rvalue *bcall0_rvalue =
              gcc_jit_context_new_rvalue_from_ptr (ctxt->ctxt,
                                                   ctxt->type_void_ptr,
                                                   call0);
            gcc_jit_rvalue *prog_ignore_rvalue =
              gcc_jit_context_new_rvalue_from_ptr (ctxt->ctxt,
                                                   ctxt->type_void_ptr,
                                                   prog_ignore);
            gcc_jit_block *is_function =
              gcc_jit_function_new_block (ctxt->cur_func, "is_function"),
              *not_function = gcc_jit_function_new_block (ctxt->cur_func,
                                                          "not_function"),
              *final = gcc_jit_function_new_block (ctxt->cur_func, "final");
            gcc_jit_lvalue *func = jit_new_local (ctxt, ctxt->type_void_ptr);

            /* if FUNCTIONP (handler) goto is_function else goto not_function; */
            gcc_jit_block_end_with_conditional (ctxt->cur_block, NULL, functionp,
                                                is_function, not_function);
            /* is_function: */
            gcc_jit_block_add_assignment (is_function, NULL, func,
                                          bcall0_rvalue);
            /* goto final */
            gcc_jit_block_end_with_jump (is_function, NULL, final);

            /* not_function: */
            gcc_jit_block_add_assignment (not_function, NULL, func,
                                          prog_ignore_rvalue);
            /* goto final */
            gcc_jit_block_end_with_jump (not_function, NULL, final);

            gcc_jit_rvalue *func_rvalue = gcc_jit_lvalue_as_rvalue (func),
              *call = jit_compile_record_unwind_protect_rvalue (ctxt,
                                                                func_rvalue,
                                                                handler);
            gcc_jit_block_add_eval (final, NULL, call);

            if (prev_block)
              gcc_jit_block_end_with_jump(prev_block, NULL, ctxt->cur_block);

            prev_block = NULL;
            ctxt->cur_block = final;
            break;
          }

        case Bcondition_case:
          {
            gcc_jit_lvalue *handlers = var_stack[stack_top--],
              *body = var_stack[stack_top--],
              *top = var_stack[stack_top];
            gcc_jit_rvalue *call =
              jit_compile_call_to_subr (ctxt, internal_lisp_condition_case, 3,
                                        gcc_jit_lvalue_as_rvalue (top),
                                        gcc_jit_lvalue_as_rvalue (body),
                                        gcc_jit_lvalue_as_rvalue (handlers));
            gcc_jit_block_add_eval (ctxt->cur_block, NULL, call);
            break;
          }

        case Bnth:
          {
            gcc_jit_lvalue *v2 = var_stack[stack_top--],
              *v1 = var_stack[stack_top];
            gcc_jit_rvalue *v2_r = gcc_jit_lvalue_as_rvalue (v2),
              *call =
              jit_compile_call_to_subr (ctxt, Fnth, 2,
                                        gcc_jit_lvalue_as_rvalue (v1), v2_r);
            gcc_jit_block_add_assignment (ctxt->cur_block, NULL, v1, call);
            call = jit_compile_assume (ctxt, jit_compile_LISTP (ctxt, v2_r));
            gcc_jit_block_add_eval (ctxt->cur_block, NULL, v2_r);
            break;
          }

        case Bsymbolp:
          {
            gcc_jit_lvalue *top = var_stack[stack_top];
            gcc_jit_rvalue *symbolp =
              jit_compile_SYMBOLP (ctxt, gcc_jit_lvalue_as_rvalue (top));
            gcc_jit_block *old_block = ctxt->cur_block;

            JIT_ADD_COMMENT ("top = SYMBOLP (top);");
            jit_compile_assign_ternary (ctxt, symbolp, top, ctxt->rvalue_t,
                                        ctxt->rvalue_nil, &ctxt->cur_block);

            if (prev_block)
              gcc_jit_block_end_with_jump (prev_block, NULL, old_block);

            prev_block = NULL;
            break;
          }

        case Bconsp:
          {
            gcc_jit_lvalue *v1 = var_stack[stack_top];
            gcc_jit_rvalue *consp =
              jit_compile_CONSP (ctxt, gcc_jit_lvalue_as_rvalue (v1));
            gcc_jit_block *old_block = ctxt->cur_block;

            JIT_ADD_COMMENT ("top = CONSP (top);");
            jit_compile_assign_ternary (ctxt, consp, v1, ctxt->rvalue_t,
                                        ctxt->rvalue_nil, &ctxt->cur_block);

            if (prev_block)
              gcc_jit_block_end_with_jump (prev_block, NULL, old_block);

            prev_block = NULL;
            break;
          }

        case Bstringp:
          {
            gcc_jit_lvalue *v1 = var_stack[stack_top];
            gcc_jit_rvalue *stringp =
              jit_compile_STRINGP (ctxt, gcc_jit_lvalue_as_rvalue (v1));
            gcc_jit_block *old_block = ctxt->cur_block;

            JIT_ADD_COMMENT ("top = STRINGP (top);");
            jit_compile_assign_ternary (ctxt, stringp, v1, ctxt->rvalue_t,
                                        ctxt->rvalue_nil, &ctxt->cur_block);

            if (prev_block)
              gcc_jit_block_end_with_jump (prev_block, NULL, old_block);

            prev_block = NULL;
            break;
          }

        case Blistp:
          {
            gcc_jit_lvalue *v1 = var_stack[stack_top];
            gcc_jit_rvalue *consp =
              jit_compile_CONSP (ctxt, gcc_jit_lvalue_as_rvalue (v1)),
              *nilp = jit_compile_NILP (ctxt, gcc_jit_lvalue_as_rvalue (v1)),
              *or = gcc_jit_context_new_binary_op (ctxt->ctxt, NULL,
                                                   GCC_JIT_BINARY_OP_LOGICAL_OR,
                                                   ctxt->type_bool, consp,
                                                   nilp);
            gcc_jit_block *old_block = ctxt->cur_block;

            JIT_ADD_COMMENT ("top = CONSP (top) || NILP (top);");
            jit_compile_assign_ternary (ctxt, or, v1, ctxt->rvalue_t,
                                        ctxt->rvalue_nil, &ctxt->cur_block);
            if (prev_block)
              gcc_jit_block_end_with_jump (prev_block, NULL, old_block);

            prev_block = NULL;
            break;
          }

        case Bnot:
          {
            gcc_jit_lvalue *v1 = var_stack[stack_top];
            gcc_jit_rvalue *nilp = jit_compile_NILP (ctxt,
                                                     gcc_jit_lvalue_as_rvalue (v1));
            gcc_jit_block *old_block = ctxt->cur_block;

            JIT_ADD_COMMENT ("top = NILP (top);");
            jit_compile_assign_ternary (ctxt, nilp, v1, ctxt->rvalue_t,
                                        ctxt->rvalue_nil, &ctxt->cur_block);

            if (prev_block)
              gcc_jit_block_end_with_jump (prev_block, NULL, old_block);

            prev_block = NULL;
            break;
          }

        case Bcons:
          {
            gcc_jit_lvalue *v1 = var_stack[stack_top--],
              *top = var_stack[stack_top];
            JIT_ADD_COMMENT ("v1 = POP; top = TOP; TOP = Fcons (top, v1)");
            gcc_jit_rvalue *top_r = gcc_jit_lvalue_as_rvalue (top),
              *call =
              jit_compile_call_to_subr (ctxt, Fcons, 2,
                                        gcc_jit_lvalue_as_rvalue (top),
                                        gcc_jit_lvalue_as_rvalue (v1));
            gcc_jit_block_add_assignment (ctxt->cur_block, NULL, top, call);
            call = jit_compile_assume (ctxt, jit_compile_CONSP (ctxt, top_r));
            gcc_jit_block_add_eval (ctxt->cur_block, NULL, call);
            break;
          }

        case Blist1:
          {
            gcc_jit_lvalue *top = var_stack[stack_top];
            gcc_jit_rvalue *top_r = gcc_jit_lvalue_as_rvalue (top),
              *call = jit_compile_call_to_subr (ctxt, list1, 1, top_r);
            gcc_jit_block_add_comment (ctxt->cur_block, NULL,
                                       "TOP = list1 (1, top)");
            gcc_jit_block_add_assignment (ctxt->cur_block, NULL, top, call);
            call = jit_compile_assume (ctxt, jit_compile_LISTP (ctxt, top_r));
            gcc_jit_block_add_eval (ctxt->cur_block, NULL, call);
            break;
          }

        case Blist2:
          {
            gcc_jit_lvalue *v1 = var_stack[stack_top--],
              *top = var_stack[stack_top];
            gcc_jit_rvalue *top_r = gcc_jit_lvalue_as_rvalue (top),
              *call =
              jit_compile_call_to_subr (ctxt, list2, 2, top_r,
                                        gcc_jit_lvalue_as_rvalue (v1));
            gcc_jit_block_add_comment (ctxt->cur_block, NULL,
                                       "v1 = POP; TOP = Flist (1, {TOP, v1})");
            gcc_jit_block_add_assignment (ctxt->cur_block, NULL, top, call);
            call = jit_compile_assume (ctxt, jit_compile_LISTP (ctxt, top_r));
            gcc_jit_block_add_eval (ctxt->cur_block, NULL, call);
            break;
          }

        case Blist3:
          {
            scratch_max_args = max (scratch_max_args, 3);
            gcc_jit_rvalue *call = jit_compile_call_to_many_subr (ctxt, 3,
                                                                  var_stack,
                                                                  stack_top,
                                                                  scratch,
                                                                  Flist);
            stack_top -= 2;
            gcc_jit_lvalue *top = var_stack[stack_top];
            gcc_jit_rvalue *top_r = gcc_jit_lvalue_as_rvalue (top);
            gcc_jit_block_add_comment (ctxt->cur_block, NULL,
                                       "TOP = Flist (3, args...)");
            gcc_jit_block_add_assignment (ctxt->cur_block, NULL, top, call);
            call = jit_compile_assume (ctxt, jit_compile_LISTP (ctxt, top_r));
            gcc_jit_block_add_eval (ctxt->cur_block, NULL, call);
            break;
          }

        case Blist4:
          {
            scratch_max_args = max (scratch_max_args, 4);
            gcc_jit_rvalue *call = jit_compile_call_to_many_subr (ctxt, 4,
                                                                  var_stack,
                                                                  stack_top,
                                                                  scratch,
                                                                  Flist);
            stack_top -= 3;
            gcc_jit_lvalue *top = var_stack[stack_top];
            gcc_jit_rvalue *top_r = gcc_jit_lvalue_as_rvalue (top);
            gcc_jit_block_add_comment (ctxt->cur_block, NULL,
                                       "TOP = Flist (4, args...)");
            gcc_jit_block_add_assignment (ctxt->cur_block, NULL, top, call);
            call = jit_compile_assume (ctxt, jit_compile_LISTP (ctxt, top_r));
            gcc_jit_block_add_eval (ctxt->cur_block, NULL, call);
            break;
          }

        case BlistN:
          {
            op = FETCH;

            scratch_max_args = max (scratch_max_args, op);
            gcc_jit_rvalue *call = jit_compile_call_to_many_subr (ctxt, op,
                                                                  var_stack,
                                                                  stack_top,
                                                                  scratch,
                                                                  Flist);
            stack_top -= op - 1;
            gcc_jit_lvalue *top = var_stack[stack_top];
            gcc_jit_rvalue *top_r = gcc_jit_lvalue_as_rvalue (top);
            sprintf (buf, "top = Flist (%d, args...)", op);
            gcc_jit_block_add_comment (ctxt->cur_block, NULL, buf);
            gcc_jit_block_add_assignment (ctxt->cur_block, NULL, top, call);
            call = jit_compile_assume (ctxt, jit_compile_LISTP (ctxt, top_r));
            gcc_jit_block_add_eval (ctxt->cur_block, NULL, call);
            break;
          }

        case Blength:
          {
            gcc_jit_lvalue *top = var_stack[stack_top];
            gcc_jit_rvalue *call =
              jit_compile_call_to_subr (ctxt, Flength, 1,
                                        gcc_jit_lvalue_as_rvalue (top));
            JIT_ADD_COMMENT ("TOP = Flength (TOP)");
            gcc_jit_block_add_assignment (ctxt->cur_block, NULL, top, call);
            break;
          }

        case Baref:
          {
            gcc_jit_lvalue *v1 = var_stack[stack_top--],
              *top = var_stack[stack_top];
            gcc_jit_rvalue *call =
              jit_compile_call_to_subr(ctxt, Faref, 2,
                                       gcc_jit_lvalue_as_rvalue (top),
                                       gcc_jit_lvalue_as_rvalue (v1));
            JIT_ADD_COMMENT ("v1 = POP; TOP = Faref (TOP, v1)");
            gcc_jit_block_add_assignment (ctxt->cur_block, NULL, top, call);
            break;
          }

        case Baset:
          {
            gcc_jit_lvalue *v2 = var_stack[stack_top--],
              *v1 = var_stack[stack_top--],
              *top = var_stack[stack_top];
            gcc_jit_rvalue *call =
              jit_compile_call_to_subr (ctxt, Faset, 3,
                                        gcc_jit_lvalue_as_rvalue (top),
                                        gcc_jit_lvalue_as_rvalue (v1),
                                        gcc_jit_lvalue_as_rvalue (v2));
            JIT_ADD_COMMENT ("v2 = POP; v1 = POP; TOP = Faset (TOP, v1, v2)");
            gcc_jit_block_add_assignment (ctxt->cur_block, NULL, top, call);
            break;
          }

        case Bsymbol_value:
          {
            gcc_jit_lvalue *top = var_stack[stack_top];
            gcc_jit_rvalue *call =
              jit_compile_call_to_subr (ctxt, Fsymbol_value, 1,
                                        gcc_jit_lvalue_as_rvalue (top));
            JIT_ADD_COMMENT ("TOP = Fsymbol_value (TOP)");
            gcc_jit_block_add_assignment (ctxt->cur_block, NULL, top, call);
            break;
          }

        case Bsymbol_function:
          {
            gcc_jit_lvalue *top = var_stack[stack_top];
            gcc_jit_rvalue *call =
              jit_compile_call_to_subr (ctxt, Fsymbol_function, 1,
                                        gcc_jit_lvalue_as_rvalue (top));
            JIT_ADD_COMMENT ("TOP = Fsymbol_function (TOP)");
            gcc_jit_block_add_assignment (ctxt->cur_block, NULL, top, call);
            break;
          }

        case Bset:
          {
            gcc_jit_lvalue *v1 = var_stack[stack_top--],
              *top = var_stack[stack_top];
            gcc_jit_rvalue *call =
              jit_compile_call_to_subr (ctxt, Fset, 2,
                                        gcc_jit_lvalue_as_rvalue (top),
                                        gcc_jit_lvalue_as_rvalue (v1));
            JIT_ADD_COMMENT ("v1 = POP; TOP = Fset (TOP, v1)");
            gcc_jit_block_add_assignment (ctxt->cur_block, NULL, top, call);
            break;
          }

        case Bfset:
          {
            gcc_jit_lvalue *v1 = var_stack[stack_top--],
              *top = var_stack[stack_top];
            gcc_jit_rvalue *call =
              jit_compile_call_to_subr (ctxt, Ffset, 2,
                                        gcc_jit_lvalue_as_rvalue (top),
                                        gcc_jit_lvalue_as_rvalue (v1));
            JIT_ADD_COMMENT ("v1 = POP; TOP = Fset (TOP, v1)");
            gcc_jit_block_add_assignment (ctxt->cur_block, NULL, top, call);
            break;
          }

        case Bget:
          {
            gcc_jit_lvalue *v1 = var_stack[stack_top--],
              *top = var_stack[stack_top];
            gcc_jit_rvalue *call =
              jit_compile_call_to_subr (ctxt, Fget, 2,
                                        gcc_jit_lvalue_as_rvalue (top),
                                        gcc_jit_lvalue_as_rvalue (v1));
            JIT_ADD_COMMENT ("v1 = POP; TOP = Fget (TOP, v1)");
            gcc_jit_block_add_assignment (ctxt->cur_block, NULL, top, call);
            break;
          }

        case Bsubstring:
          {
            gcc_jit_lvalue *v2 = var_stack[stack_top--],
              *v1 = var_stack[stack_top--], *top = var_stack[stack_top];
            gcc_jit_rvalue *call =
              jit_compile_call_to_subr (ctxt, Fsubstring, 3,
                                        gcc_jit_lvalue_as_rvalue (top),
                                        gcc_jit_lvalue_as_rvalue (v1),
                                        gcc_jit_lvalue_as_rvalue (v2));
            JIT_ADD_COMMENT ("v2 = POP; v1 = POP; TOP = Fsubstring (TOP, v1, v2)");
            gcc_jit_block_add_assignment (ctxt->cur_block, NULL, top, call);
            break;
          }

#define JIT_COMPILE_CONCAT(O)                                           \
          do {                                                          \
            scratch_max_args = max (scratch_max_args, (O));             \
            gcc_jit_rvalue *__call =                                    \
              jit_compile_call_to_many_subr (ctxt, (O),                 \
                                             var_stack,                 \
                                             stack_top,                 \
                                             scratch,                   \
                                             Fconcat);                  \
            gcc_jit_lvalue *__top = var_stack[stack_top];               \
            stack_top -= (O) - 1;                                       \
            gcc_jit_block_add_comment (ctxt->cur_block, NULL,           \
                                       "TOP = Fconcat ("#O", args...)"); \
            gcc_jit_block_add_assignment (ctxt->cur_block, NULL, __top, \
                                          __call);                      \
          } while(0);

        case Bconcat2:
          JIT_COMPILE_CONCAT (2);
          break;

        case Bconcat3:
          JIT_COMPILE_CONCAT (3);
          break;

        case Bconcat4:
          JIT_COMPILE_CONCAT (4);
          break;

        case BconcatN:
          op = FETCH;
          JIT_COMPILE_CONCAT (op);
          break;
#undef JIT_COMPILE_CONCAT

        case Bsub1:
          {
            gcc_jit_lvalue *top = var_stack[stack_top];
            gcc_jit_rvalue *sub1 =
              jit_compile_call_to_subr (ctxt, Fsub1, 1,
                                        gcc_jit_lvalue_as_rvalue (top));
            JIT_ADD_COMMENT ("TOP = Fsub1 (TOP);");
            gcc_jit_block_add_assignment (ctxt->cur_block, NULL, top, sub1);
            break;
          }

        case Badd1:
          {
            gcc_jit_lvalue *top = var_stack[stack_top];
            gcc_jit_rvalue *add1 =
              jit_compile_call_to_subr (ctxt, Fadd1, 1,
                                        gcc_jit_lvalue_as_rvalue (top));
            JIT_ADD_COMMENT ("TOP = Fadd1 (TOP)");
            gcc_jit_block_add_assignment (ctxt->cur_block, NULL, top, add1);
            break;
          }

        case Beqlsign:
          {
            gcc_jit_lvalue *v2 = var_stack[stack_top--],
              *top = var_stack[stack_top]; /* top */
            JIT_ADD_COMMENT ("v2 = POP; TOP = arithcompare (TOP, v2, ARITH_EQUAL)");
            gcc_jit_rvalue *call =
              jit_compile_arithcompare (ctxt, gcc_jit_lvalue_as_rvalue (top),
                                        gcc_jit_lvalue_as_rvalue (v2),
                                        ARITH_EQUAL);
            gcc_jit_block_add_assignment (ctxt->cur_block, NULL, top, call);
            break;
          }

        case Bgtr:
          {
            gcc_jit_lvalue *v1 = var_stack[stack_top--],
              *top = var_stack[stack_top];
            JIT_ADD_COMMENT ("v1 = POP; TOP = arithcompare (TOP, v1, ARITH_GRTR)");
            gcc_jit_rvalue *call =
              jit_compile_arithcompare (ctxt, gcc_jit_lvalue_as_rvalue (top),
                                        gcc_jit_lvalue_as_rvalue (v1),
                                        ARITH_GRTR);
            gcc_jit_block_add_assignment (ctxt->cur_block, NULL, top, call);
            break;
          }

        case Blss:
          {
            gcc_jit_lvalue *v1 = var_stack[stack_top--],
              *top = var_stack[stack_top];
            JIT_ADD_COMMENT ("v1 = POP; TOP = arithcompare (TOP, v1, ARITH_LESS)");
            gcc_jit_rvalue *call =
              jit_compile_arithcompare (ctxt, gcc_jit_lvalue_as_rvalue (top),
                                        gcc_jit_lvalue_as_rvalue (v1),
                                        ARITH_LESS);
            gcc_jit_block_add_assignment (ctxt->cur_block, NULL, top, call);
            break;
          }

        case Bleq:
          {
            gcc_jit_lvalue *v1 = var_stack[stack_top--],
              *top = var_stack[stack_top];
            JIT_ADD_COMMENT ("v1 = POP; TOP = arithcompare (TOP, v1, ARITH_LESS_OR_EQUAL)");
            gcc_jit_rvalue *call =
              jit_compile_arithcompare (ctxt, gcc_jit_lvalue_as_rvalue (top),
                                        gcc_jit_lvalue_as_rvalue (v1),
                                        ARITH_LESS_OR_EQUAL);
            gcc_jit_block_add_assignment (ctxt->cur_block, NULL, top, call);
              break;
          }

        case Bgeq:
          {
            gcc_jit_lvalue *v1 = var_stack[stack_top--],
              *top = var_stack[stack_top];
            JIT_ADD_COMMENT ("v1 = POP; TOP = arithcompare (TOP, v1, ARITH_GRTR_OR_EQUAL)");
            gcc_jit_rvalue *call =
              jit_compile_arithcompare (ctxt, gcc_jit_lvalue_as_rvalue (top),
                                        gcc_jit_lvalue_as_rvalue (v1),
                                        ARITH_GRTR_OR_EQUAL);
            gcc_jit_block_add_assignment (ctxt->cur_block, NULL, top, call);
            break;
          }

        case Bmax:
          {
            gcc_jit_lvalue *v1 = var_stack[stack_top--],
              *top = var_stack[stack_top];
            gcc_jit_rvalue *call =
              jit_compile_minmax_driver (ctxt, ARITH_GRTR,
                                         gcc_jit_lvalue_as_rvalue (top),
                                         gcc_jit_lvalue_as_rvalue (v1));
            gcc_jit_block_add_assignment (ctxt->cur_block, NULL, top, call);
            break;
          }

        case Bmin:
          {
            gcc_jit_lvalue *v1 = var_stack[stack_top--],
              *top = var_stack[stack_top];
            gcc_jit_rvalue *call =
              jit_compile_minmax_driver (ctxt, ARITH_LESS,
                                         gcc_jit_lvalue_as_rvalue (top),
                                         gcc_jit_lvalue_as_rvalue (v1));
            gcc_jit_block_add_assignment (ctxt->cur_block, NULL, top, call);
            break;
          }

        case Brem:
          {
            gcc_jit_lvalue *v1 = var_stack[stack_top--],
              *top = var_stack[stack_top];
            JIT_ADD_COMMENT ("v1 = POP; TOP = Frem (TOP, v1)");
            gcc_jit_rvalue *call =
              jit_compile_call_to_subr (ctxt, Frem, 2,
                                        gcc_jit_lvalue_as_rvalue (top),
                                        gcc_jit_lvalue_as_rvalue (v1));
            gcc_jit_block_add_assignment (ctxt->cur_block, NULL, top, call);
            break;
          }

        case Bpoint:
          {
            gcc_jit_lvalue *top = var_stack[++stack_top];
            JIT_ADD_COMMENT ("PUSH (native_point ())");
            gcc_jit_rvalue *call =
              jit_compile_call_to_subr (ctxt, native_point, 0);
            gcc_jit_block_add_assignment (ctxt->cur_block, NULL, top, call);
            break;
          }

        case Bgoto_char:
          {
            gcc_jit_lvalue *top = var_stack[stack_top];
            JIT_ADD_COMMENT ("TOP = Fgoto_char (TOP)");
            gcc_jit_rvalue *call =
              jit_compile_call_to_subr (ctxt, Fgoto_char, 1,
                                        gcc_jit_lvalue_as_rvalue (top));
            gcc_jit_block_add_assignment (ctxt->cur_block, NULL, top, call);
            break;
          }

        case Binsert:
          {
            JIT_ADD_COMMENT ("TOP = Finsert (1, TOP)");
            scratch_max_args = max (scratch_max_args, 1);
            gcc_jit_rvalue *call = jit_compile_call_to_many_subr (ctxt, 1,
                                                                  var_stack,
                                                                  stack_top,
                                                                  scratch,
                                                                  Finsert);
            gcc_jit_lvalue *top = var_stack[stack_top];
            gcc_jit_block_add_assignment (ctxt->cur_block, NULL, top, call);
            break;
          }

        case BinsertN:
          {
            op = FETCH;
            scratch_max_args = max (scratch_max_args, op);
            gcc_jit_rvalue *call = jit_compile_call_to_many_subr (ctxt, op,
                                                                  var_stack,
                                                                  stack_top,
                                                                  scratch,
                                                                  Finsert);
            stack_top -= op - 1;
            gcc_jit_lvalue *top = var_stack[stack_top];
            sprintf (buf, "top = Finsert (%d, args...)", op + 1);
            gcc_jit_block_add_comment (ctxt->cur_block, NULL, buf);
            gcc_jit_block_add_assignment (ctxt->cur_block, NULL, top, call);
            break;
          }

        case Bpoint_max:
          {
            gcc_jit_lvalue *top = var_stack[++stack_top];
            JIT_ADD_COMMENT ("PUSH (Fpoint_max ())");
            gcc_jit_rvalue *call =
              jit_compile_call_to_subr (ctxt, Fpoint_max, 0);
            gcc_jit_block_add_assignment (ctxt->cur_block, NULL, top, call);
            break;
          }

        case Bpoint_min:
          {
            gcc_jit_lvalue *top = var_stack[++stack_top];
            JIT_ADD_COMMENT ("PUSH (Fpoint_min ())");
            gcc_jit_rvalue *call =
              jit_compile_call_to_subr (ctxt, Fpoint_min, 0);
            gcc_jit_block_add_assignment (ctxt->cur_block, NULL, top, call);
            break;
          }

        case Bchar_after:
          {
            gcc_jit_lvalue *top = var_stack[stack_top];
            JIT_ADD_COMMENT ("TOP = Fchar_after (TOP)");
            gcc_jit_rvalue *call =
              jit_compile_call_to_subr (ctxt, Fchar_after, 1,
                                        gcc_jit_lvalue_as_rvalue (top));
            gcc_jit_block_add_assignment (ctxt->cur_block, NULL, top, call);
            break;
          }

        case Bfollowing_char:
          {
            gcc_jit_lvalue *top = var_stack[++stack_top];
            JIT_ADD_COMMENT ("TOP = Ffollowing_char ()");
            gcc_jit_rvalue *call =
              jit_compile_call_to_subr (ctxt, Ffollowing_char, 0);
            gcc_jit_block_add_assignment (ctxt->cur_block, NULL, top, call);
            break;
          }

        case Bpreceding_char:
          {
            gcc_jit_lvalue *top = var_stack[++stack_top];
            JIT_ADD_COMMENT ("TOP = Fprevious_char ()");
            gcc_jit_rvalue *call =
              jit_compile_call_to_subr (ctxt, Fprevious_char, 0);
            gcc_jit_block_add_assignment (ctxt->cur_block, NULL, top, call);
            break;
          }

        case Bcurrent_column:
          {
            gcc_jit_lvalue *top = var_stack[++stack_top];
            JIT_ADD_COMMENT ("TOP = native_current_column ()");
            gcc_jit_rvalue *call =
              jit_compile_call_to_subr (ctxt, native_current_column, 0);
            gcc_jit_block_add_assignment (ctxt->cur_block, NULL, top, call);
            break;
          }

        case Bindent_to:
          {
            gcc_jit_lvalue *top = var_stack[stack_top];
            JIT_ADD_COMMENT ("TOP = Findent_to (TOP, Qnil)");
            gcc_jit_rvalue *call =
              jit_compile_call_to_subr (ctxt, Findent_to, 2,
                                        gcc_jit_lvalue_as_rvalue (top),
                                        ctxt->rvalue_nil);
            gcc_jit_block_add_assignment (ctxt->cur_block, NULL, top, call);
            break;
          }

        case Beolp:
          {
            gcc_jit_lvalue *top = var_stack[++stack_top];
            gcc_jit_rvalue *call =
              jit_compile_call_to_subr (ctxt, Feolp, 0);
            JIT_ADD_COMMENT ("TOP = Feolp ()");
            gcc_jit_block_add_assignment (ctxt->cur_block, NULL, top, call);
            break;
          }

        case Beobp:
          {
            gcc_jit_lvalue *top = var_stack[++stack_top];
            gcc_jit_rvalue *call =
              jit_compile_call_to_subr (ctxt, Feobp, 0);
            JIT_ADD_COMMENT ("TOP = Feobp ()");
            gcc_jit_block_add_assignment (ctxt->cur_block, NULL, top, call);
            break;
          }

        case Bbolp:
          {
            gcc_jit_lvalue *top = var_stack[++stack_top];
            gcc_jit_rvalue *call =
              jit_compile_call_to_subr (ctxt, Fbolp, 0);
            JIT_ADD_COMMENT ("TOP = Fbolp ()");
            gcc_jit_block_add_assignment (ctxt->cur_block, NULL, top, call);
            break;
          }

        case Bbobp:
          {
            gcc_jit_lvalue *top = var_stack[++stack_top];
            gcc_jit_rvalue *call =
              jit_compile_call_to_subr (ctxt, Fbobp, 0);
            JIT_ADD_COMMENT ("TOP = Fbobp ()");
            gcc_jit_block_add_assignment (ctxt->cur_block, NULL, top, call);
            break;
          }

        case Bcurrent_buffer:
          {
            gcc_jit_lvalue *top = var_stack[++stack_top];
            gcc_jit_rvalue *call =
              jit_compile_call_to_subr (ctxt, Fcurrent_buffer, 0);
            JIT_ADD_COMMENT ("TOP = Fcurrent_buffer ()");
            gcc_jit_block_add_assignment (ctxt->cur_block, NULL, top, call);
            break;
          }

        case Bset_buffer:
          {
            gcc_jit_lvalue *top = var_stack[stack_top];
            gcc_jit_rvalue *call =
              jit_compile_call_to_subr (ctxt, Fset_buffer, 1,
                                        gcc_jit_lvalue_as_rvalue (top));
            JIT_ADD_COMMENT ("TOP = Fset_buffer (TOP)");
            gcc_jit_block_add_assignment (ctxt->cur_block, NULL, top, call);
            break;
          }

        case Binteractive_p:
          {
            Lisp_Object interactive_p = intern ("interactive-p");
            gcc_jit_lvalue *top = var_stack[++stack_top];
            gcc_jit_rvalue
              *interative_rvalue =
              jit_new_rvalue_from_lisp_object (ctxt, interactive_p),
              *call =
              jit_compile_call_to_subr (ctxt, call0, 1,
                                        interative_rvalue);
            JIT_ADD_COMMENT ("TOP = call0 (intern (\"interactive-p\"))");
            gcc_jit_block_add_assignment (ctxt->cur_block, NULL, top, call);
            break;
          }

        case Bforward_char:
          {
            gcc_jit_lvalue *top = var_stack[++stack_top];
            gcc_jit_rvalue *call =
              jit_compile_call_to_subr (ctxt, Fforward_char, 0);
            JIT_ADD_COMMENT ("TOP = Fforward_char ()");
            gcc_jit_block_add_assignment (ctxt->cur_block, NULL, top, call);
            break;
          }

        case Bforward_word:
          {
            gcc_jit_lvalue *top = var_stack[++stack_top];
            gcc_jit_rvalue *call =
              jit_compile_call_to_subr (ctxt, Fforward_word, 0);
            JIT_ADD_COMMENT ("TOP = Fforward_word ()");
            gcc_jit_block_add_assignment (ctxt->cur_block, NULL, top, call);
            break;
          }

        case Bskip_chars_forward:
          {
            gcc_jit_lvalue *v1 = var_stack[stack_top--],
              *top = var_stack[stack_top];
            gcc_jit_rvalue *call =
              jit_compile_call_to_subr (ctxt, Fskip_chars_forward, 2,
                                        gcc_jit_lvalue_as_rvalue (top),
                                        gcc_jit_lvalue_as_rvalue (v1));
            JIT_ADD_COMMENT ("v1 = POP; TOP = Fskip_chars_forward (TOP, POP)");
            gcc_jit_block_add_assignment (ctxt->cur_block, NULL, top, call);
            break;
          }

        case Bskip_chars_backward:
          {
            gcc_jit_lvalue *v1 = var_stack[stack_top--],
              *top = var_stack[stack_top];
            gcc_jit_rvalue *call =
              jit_compile_call_to_subr (ctxt, Fskip_chars_backward, 2,
                                        gcc_jit_lvalue_as_rvalue (top),
                                        gcc_jit_lvalue_as_rvalue (v1));
            JIT_ADD_COMMENT ("v1 = POP; TOP = Fskip_chars_backward (TOP, POP)");
            gcc_jit_block_add_assignment (ctxt->cur_block, NULL, top, call);
            break;
          }

        case Bforward_line:
          {
            gcc_jit_lvalue *top = var_stack[stack_top];
            gcc_jit_rvalue *call =
              jit_compile_call_to_subr (ctxt, Fforward_line, 1,
                                        gcc_jit_lvalue_as_rvalue (top));
            JIT_ADD_COMMENT ("TOP = Fforward_line (TOP)");
            gcc_jit_block_add_assignment (ctxt->cur_block, NULL, top, call);
            break;
          }

        case Bchar_syntax:
          {
            gcc_jit_lvalue *top = var_stack[stack_top];
            gcc_jit_rvalue *call =
              jit_compile_call_to_subr (ctxt, native_char_syntax, 1,
                                        gcc_jit_lvalue_as_rvalue (top));
            JIT_ADD_COMMENT ("TOP = native_char_syntax (TOP)");
            gcc_jit_block_add_assignment(ctxt->cur_block, NULL, top, call);
            break;
          }

        case Bbuffer_substring:
          {
            gcc_jit_lvalue *v1 = var_stack[stack_top--],
              *top = var_stack[stack_top];
            gcc_jit_rvalue *call =
              jit_compile_call_to_subr (ctxt, Fbuffer_substring, 2,
                                        gcc_jit_lvalue_as_rvalue (top),
                                        gcc_jit_lvalue_as_rvalue (v1));
            JIT_ADD_COMMENT ("v1 = POP; TOP = Fbuffer_string (TOP, v1)");
            gcc_jit_block_add_assignment (ctxt->cur_block, NULL, top, call);
            break;
          }

        case Bdelete_region:
          {
            gcc_jit_lvalue *v1 = var_stack[stack_top--],
              *top = var_stack[stack_top];
            gcc_jit_rvalue *call =
              jit_compile_call_to_subr (ctxt, Fdelete_region, 2,
                                        gcc_jit_lvalue_as_rvalue (top),
                                        gcc_jit_lvalue_as_rvalue (v1));
            JIT_ADD_COMMENT ("v1 = POP; TOP = Fdelete_region (TOP, v1)");
            gcc_jit_block_add_assignment (ctxt->cur_block, NULL, top, call);
            break;
          }

        case Bnarrow_to_region:
          {
            gcc_jit_lvalue *v1 = var_stack[stack_top--],
              *top = var_stack[stack_top];
            gcc_jit_rvalue *call =
              jit_compile_call_to_subr (ctxt, Fnarrow_to_region, 2,
                                        gcc_jit_lvalue_as_rvalue (top),
                                        gcc_jit_lvalue_as_rvalue (v1));
            JIT_ADD_COMMENT ("v1 = POP; TOP = Fnarrow_to_region (TOP, v1)");
            gcc_jit_block_add_assignment (ctxt->cur_block, NULL, top, call);
            break;
          }

        case Bwiden:
          {
            gcc_jit_lvalue *top = var_stack[++stack_top];
            gcc_jit_rvalue *call =
              jit_compile_call_to_subr (ctxt, Fwiden, 0);
            JIT_ADD_COMMENT ("TOP = Fwiden ()");
            gcc_jit_block_add_assignment (ctxt->cur_block, NULL, top, call);
            break;
          }

        case Bend_of_line:
          {
            gcc_jit_lvalue *top = var_stack[stack_top];
            gcc_jit_rvalue *call =
              jit_compile_call_to_subr (ctxt, Fend_of_line, 1,
                                        gcc_jit_lvalue_as_rvalue (top));
            JIT_ADD_COMMENT ("TOP = Fend_of_line (TOP)");
            gcc_jit_block_add_assignment (ctxt->cur_block, NULL, top, call);
            break;
          }

        case Bset_marker:
          {
            gcc_jit_lvalue *v2 = var_stack[stack_top--],
              *v1 = var_stack[stack_top--],
              *top = var_stack[stack_top];
            gcc_jit_rvalue *call =
              jit_compile_call_to_subr (ctxt, Fset_marker, 3,
                                        gcc_jit_lvalue_as_rvalue (top),
                                        gcc_jit_lvalue_as_rvalue (v1),
                                        gcc_jit_lvalue_as_rvalue (v2));
            JIT_ADD_COMMENT ("v1 = POP; v2 = POP; TOP = Fset_marker (TOP, v1, v2)");
            gcc_jit_block_add_assignment (ctxt->cur_block, NULL, top, call);
            break;
          }

        case Bmatch_beginning:
          {
            gcc_jit_lvalue *top = var_stack[stack_top];
            gcc_jit_rvalue *call =
              jit_compile_call_to_subr (ctxt, Fmatch_beginning, 1,
                                        gcc_jit_lvalue_as_rvalue (top));
            JIT_ADD_COMMENT ("TOP = Fmatch_beginning (TOP)");
            gcc_jit_block_add_assignment (ctxt->cur_block, NULL, top, call);
            break;
          }

        case Bmatch_end:
          {
            gcc_jit_lvalue *top = var_stack[stack_top];
            gcc_jit_rvalue *call =
              jit_compile_call_to_subr (ctxt, Fmatch_end, 1,
                                        gcc_jit_lvalue_as_rvalue (top));
            JIT_ADD_COMMENT ("TOP = Fmatch_end (TOP)");
            gcc_jit_block_add_assignment (ctxt->cur_block, NULL, top, call);
            break;
          }

        case Bupcase:
          {
            gcc_jit_lvalue *top = var_stack[stack_top];
            gcc_jit_rvalue *call =
              jit_compile_call_to_subr (ctxt, Fupcase, 1,
                                        gcc_jit_lvalue_as_rvalue (top));
            JIT_ADD_COMMENT ("TOP = Fupcase (TOP)");
            gcc_jit_block_add_assignment (ctxt->cur_block, NULL, top, call);
            break;
          }

        case Bdowncase:
          {
            gcc_jit_lvalue *top = var_stack[stack_top];
            gcc_jit_rvalue *call =
              jit_compile_call_to_subr (ctxt, Fdowncase, 1,
                                        gcc_jit_lvalue_as_rvalue (top));
            JIT_ADD_COMMENT ("TOP = Fdowncase (TOP)");
            gcc_jit_block_add_assignment (ctxt->cur_block, NULL, top, call);
            break;
          }

        case Bstringeqlsign:
          {
            gcc_jit_lvalue *v1 = var_stack[stack_top--],
              *top = var_stack[stack_top];
            gcc_jit_rvalue *call =
              jit_compile_call_to_subr (ctxt, Fstring_equal, 2,
                                        gcc_jit_lvalue_as_rvalue (top),
                                        gcc_jit_lvalue_as_rvalue (v1));
            JIT_ADD_COMMENT ("v1 = POP; TOP = Fstring_equal (TOP, v1)");
            gcc_jit_block_add_assignment (ctxt->cur_block, NULL, top, call);
            break;
          }

        case Bstringlss:
          {
            gcc_jit_lvalue *v1 = var_stack[stack_top--],
              *top = var_stack[stack_top];
            gcc_jit_rvalue *call =
              jit_compile_call_to_subr (ctxt, Fstring_lessp, 2,
                                        gcc_jit_lvalue_as_rvalue (top),
                                        gcc_jit_lvalue_as_rvalue (v1));
            JIT_ADD_COMMENT ("v1 = POP; Fstring_lessp (TOP, v1)");
            gcc_jit_block_add_assignment (ctxt->cur_block, NULL, top, call);
            break;
          }

        case Bequal:
          {
            gcc_jit_lvalue *v1 = var_stack[stack_top--],
              *top = var_stack[stack_top];
            gcc_jit_rvalue *call =
              jit_compile_call_to_subr (ctxt, Fequal, 2,
                                        gcc_jit_lvalue_as_rvalue (top),
                                        gcc_jit_lvalue_as_rvalue (v1));
            JIT_ADD_COMMENT ("v1 = POP; Fequal (TOP, v1)");
            gcc_jit_block_add_assignment (ctxt->cur_block, NULL, top, call);
            break;
          }

        case Bnthcdr:
          {
            gcc_jit_lvalue *v1 = var_stack[stack_top--],
              *top = var_stack[stack_top];
            gcc_jit_rvalue *call =
              jit_compile_call_to_subr (ctxt, Fnthcdr, 2,
                                        gcc_jit_lvalue_as_rvalue (top),
                                        gcc_jit_lvalue_as_rvalue (v1));
            JIT_ADD_COMMENT ("v1 = POP; Fnthcdr (TOP, v1)");
            gcc_jit_block_add_assignment (ctxt->cur_block, NULL, top, call);
            break;
          }

        case Belt:
          {
            gcc_jit_lvalue *v1 = var_stack[stack_top--],
              *top = var_stack[stack_top];
            gcc_jit_rvalue *call =
              jit_compile_call_to_subr (ctxt, Felt, 2,
                                        gcc_jit_lvalue_as_rvalue (top),
                                        gcc_jit_lvalue_as_rvalue (v1));
            JIT_ADD_COMMENT ("v1 = POP; TOP = Felt (TOP, v1)");
            gcc_jit_block_add_assignment (ctxt->cur_block, NULL, top, call);
            break;
          }

        case Bmember:
          {
            gcc_jit_lvalue *v1 = var_stack[stack_top--],
              *top = var_stack[stack_top];
            gcc_jit_rvalue *call =
              jit_compile_call_to_subr (ctxt, Fmember, 2,
                                        gcc_jit_lvalue_as_rvalue (top),
                                        gcc_jit_lvalue_as_rvalue (v1));
            JIT_ADD_COMMENT ("v1 = POP; TOP = Fmember (TOP, v1)");
            gcc_jit_block_add_assignment (ctxt->cur_block, NULL, top, call);
            break;
          }

        case Bassq:
          {
            gcc_jit_lvalue *v1 = var_stack[stack_top--],
              *top = var_stack[stack_top];
            gcc_jit_rvalue *call =
              jit_compile_call_to_subr (ctxt, Fassq, 2,
                                        gcc_jit_lvalue_as_rvalue (top),
                                        gcc_jit_lvalue_as_rvalue (v1));
            JIT_ADD_COMMENT ("v1 = POP; TOP = Fassq (TOP, v1)");
            gcc_jit_block_add_assignment (ctxt->cur_block, NULL, top, call);
            break;
          }

        case Bnreverse:
          {
            gcc_jit_lvalue *top = var_stack[stack_top];
            gcc_jit_rvalue *call =
              jit_compile_call_to_subr (ctxt, Fnreverse, 1,
                                        gcc_jit_lvalue_as_rvalue (top));
            JIT_ADD_COMMENT ("TOP = Fnreverse (TOP)");
            gcc_jit_block_add_assignment (ctxt->cur_block, NULL, top, call);
            break;
          }

        case Bsetcar:
          {
            gcc_jit_lvalue *v1 = var_stack[stack_top--],
              *top = var_stack[stack_top];
            gcc_jit_rvalue *call =
              jit_compile_call_to_subr (ctxt, Fsetcar, 2,
                                        gcc_jit_lvalue_as_rvalue (top),
                                        gcc_jit_lvalue_as_rvalue (v1));
            JIT_ADD_COMMENT ("v1 = POP; TOP = Fsetcar (TOP, v1)");
            gcc_jit_block_add_assignment (ctxt->cur_block, NULL, top, call);
            break;
          }

        case Bsetcdr:
          {
            gcc_jit_lvalue *v1 = var_stack[stack_top--],
              *top = var_stack[stack_top];
            gcc_jit_rvalue *call =
              jit_compile_call_to_subr (ctxt, Fsetcdr, 2,
                                        gcc_jit_lvalue_as_rvalue (top),
                                        gcc_jit_lvalue_as_rvalue (v1));
            JIT_ADD_COMMENT ("v1 = POP; TOP = Fsetcdr (TOP, v1)");
            gcc_jit_block_add_assignment (ctxt->cur_block, NULL, top, call);
            break;
          }

        case Bcar_safe:
          {
            gcc_jit_lvalue *top = var_stack[stack_top];
            gcc_jit_rvalue *consp =
              jit_compile_CONSP (ctxt, gcc_jit_lvalue_as_rvalue (top)), *xcar;
            gcc_jit_block  *is_consp =
              gcc_jit_function_new_block (ctxt->cur_func, "consp"),
              *is_not_consp = gcc_jit_function_new_block (ctxt->cur_func,
                                                         "not_consp"),
              *final_block = gcc_jit_function_new_block (ctxt->cur_func,
                                                         "final");

            if (prev_block)
              gcc_jit_block_end_with_jump (prev_block, NULL, ctxt->cur_block);

            gcc_jit_block_end_with_conditional (ctxt->cur_block, NULL, consp,
                                                is_consp, is_not_consp);
            ctxt->cur_block = is_consp;
            xcar = jit_compile_XCAR (ctxt, gcc_jit_lvalue_as_rvalue (top));
            gcc_jit_block_add_assignment (ctxt->cur_block, NULL, top, xcar);
            gcc_jit_block_end_with_jump (ctxt->cur_block, NULL, final_block);

            ctxt->cur_block = is_not_consp;
            gcc_jit_block_add_assignment (is_not_consp, NULL, top,
                                          ctxt->rvalue_nil);
            gcc_jit_block_end_with_jump (ctxt->cur_block, NULL, final_block);

            ctxt->cur_block = final_block;
            prev_block = NULL;
            break;
          }

        case Bcdr_safe:
          {
            gcc_jit_lvalue *top = var_stack[stack_top];
            gcc_jit_rvalue *consp =
              jit_compile_CONSP (ctxt, gcc_jit_lvalue_as_rvalue (top)), *xcar;
            gcc_jit_block  *is_consp =
              gcc_jit_function_new_block (ctxt->cur_func, "consp"),
              *is_not_consp = gcc_jit_function_new_block (ctxt->cur_func,
                                                         "not_consp"),
              *final_block = gcc_jit_function_new_block (ctxt->cur_func,
                                                         "final");

            if (prev_block)
              gcc_jit_block_end_with_jump (prev_block, NULL, ctxt->cur_block);

            gcc_jit_block_end_with_conditional (ctxt->cur_block, NULL, consp,
                                                is_consp, is_not_consp);
            ctxt->cur_block = is_consp;
            xcar = jit_compile_XCDR (ctxt, gcc_jit_lvalue_as_rvalue (top));
            gcc_jit_block_add_assignment (ctxt->cur_block, NULL, top, xcar);
            gcc_jit_block_end_with_jump (ctxt->cur_block, NULL, final_block);

            ctxt->cur_block = is_not_consp;
            gcc_jit_block_add_assignment (is_not_consp, NULL, top,
                                          ctxt->rvalue_nil);
            gcc_jit_block_end_with_jump (ctxt->cur_block, NULL, final_block);

            ctxt->cur_block = final_block;
            prev_block = NULL;
            break;
          }

        case Bnconc:
          {
            scratch_max_args = max (scratch_max_args, 2);
            gcc_jit_rvalue *call = jit_compile_call_to_many_subr (ctxt, 2,
                                                                  var_stack,
                                                                  stack_top,
                                                                  scratch,
                                                                  Fnconc);
            stack_top--;
            gcc_jit_lvalue *top = var_stack[stack_top];
            JIT_ADD_COMMENT ("TOP = Fnconc (2, ...)");
            gcc_jit_block_add_assignment (ctxt->cur_block, NULL, top, call);
            break;
          }

        case Bnumberp:
          {
            gcc_jit_lvalue *top = var_stack[stack_top];
            gcc_jit_rvalue *numberp =
              jit_compile_NUMBERP (ctxt, gcc_jit_lvalue_as_rvalue (top));
            gcc_jit_block *old_block = ctxt->cur_block;

            JIT_ADD_COMMENT ("TOP = NUMBERP (TOP)");
            jit_compile_assign_ternary (ctxt, numberp, top,
                                        ctxt->rvalue_t, ctxt->rvalue_nil,
                                        &(ctxt->cur_block));

            if (prev_block)
              gcc_jit_block_end_with_jump (prev_block, NULL, old_block);

            prev_block = NULL;
            break;
          }

        case Bintegerp:
          {
            gcc_jit_lvalue *top = var_stack[stack_top];
            gcc_jit_rvalue *integerp =
              jit_compile_INTEGERP (ctxt, gcc_jit_lvalue_as_rvalue (top));
            gcc_jit_block *old_block = ctxt->cur_block;

            JIT_ADD_COMMENT ("TOP = INTEGERP (TOP)");
            jit_compile_assign_ternary (ctxt, integerp, top,
                                        ctxt->rvalue_t, ctxt->rvalue_nil,
                                        &(ctxt->cur_block));

            if (prev_block)
              gcc_jit_block_end_with_jump (prev_block, NULL, old_block);

            prev_block = NULL;
            break;
          }

        case Bstack_ref1:
        case Bstack_ref2:
        case Bstack_ref3:
        case Bstack_ref4:
        case Bstack_ref5:
          {
            gcc_jit_lvalue *v1 = var_stack[stack_top + (Bstack_ref - op)],
              *top = var_stack[++stack_top];
            gcc_jit_block_add_assignment (ctxt->cur_block, NULL, top,
                                          gcc_jit_lvalue_as_rvalue (v1));
            break;
          }

        case Bstack_ref6:
          {
            gcc_jit_lvalue *v1 = var_stack[stack_top - FETCH],
              *top = var_stack[++stack_top];
            gcc_jit_block_add_assignment (ctxt->cur_block, NULL, top,
                                          gcc_jit_lvalue_as_rvalue (v1));
            break;
          }

        case Bstack_ref7:
          {
            gcc_jit_lvalue *v1 = var_stack[stack_top - FETCH2],
              *top = var_stack[++stack_top];
            gcc_jit_block_add_assignment (ctxt->cur_block, NULL, top,
                                          gcc_jit_lvalue_as_rvalue (v1));
            break;
          }

        case Bstack_set:
          {
            int index = stack_top - FETCH;
            gcc_jit_lvalue *top = var_stack[stack_top--];
            gcc_jit_block_add_assignment (ctxt->cur_block, NULL,
                                          var_stack[index],
                                          gcc_jit_lvalue_as_rvalue (top));
            break;
          }

        case Bstack_set2:
          {
            int index = stack_top - FETCH2;
            gcc_jit_lvalue *top = var_stack[stack_top--];
            gcc_jit_block_add_assignment (ctxt->cur_block, NULL,
                                          var_stack[index],
                                          gcc_jit_lvalue_as_rvalue (top));
            break;
          }

        case BdiscardN:
          {
            op = FETCH;
            gcc_jit_lvalue *top = var_stack[stack_top];

            if (op & 0x80)
              {
                op &= 0x7F;
                gcc_jit_block_add_assignment (ctxt->cur_block, NULL,
                                              var_stack[stack_top - op],
                                              gcc_jit_lvalue_as_rvalue (top));
              }
            stack_top = stack_top - op;
            break;
          }

        case Bif:
          {
            gcc_jit_lvalue *top = var_stack[stack_top--];
            gcc_jit_rvalue *top_not_nil =
              jit_compile_not_NILP(ctxt, gcc_jit_lvalue_as_rvalue (top));
            gcc_jit_block *when_true =
              gcc_jit_function_new_block (ctxt->cur_func, "when_true"),
              *when_false = gcc_jit_function_new_block (ctxt->cur_func,
                                                        "when_false"),
              *final_block = gcc_jit_function_new_block (ctxt->cur_func,
                                                         "final_block");
            jit_block_stack_push_if (block_stack, when_false, final_block);
            gcc_jit_block_end_with_conditional (ctxt->cur_block, NULL,
                                                top_not_nil, when_true,
                                                when_false);
            if (prev_block && prev_block != ctxt->cur_block)
              gcc_jit_block_end_with_jump (prev_block, NULL, ctxt->cur_block);

            ctxt->cur_block = when_true;
            prev_block = NULL;
            break;
          }
        case Belse:
          {
            stack_top--;
            struct jit_block *block = jit_block_stack_top (block_stack);
            eassert (block->type == JIT_BLOCK_IF);
            block->type = JIT_BLOCK_ELSE;
            gcc_jit_block_end_with_jump (ctxt->cur_block, NULL,
                                         block->continuation_block);

            if (prev_block && prev_block != ctxt->cur_block)
              gcc_jit_block_end_with_jump (prev_block, NULL, ctxt->cur_block);

            ctxt->cur_block = block->else_block;
            prev_block = NULL;
            break;
          }
        case Bend:
          {
            struct jit_block *block = jit_block_stack_pop (block_stack);

            switch (block->type)
              {
              case JIT_BLOCK:
                gcc_jit_block_end_with_jump (ctxt->cur_block, NULL,
                                             block->continuation_block);
                if (prev_block && prev_block != ctxt->cur_block)
                  gcc_jit_block_end_with_jump (prev_block, NULL,
                                               ctxt->cur_block);
                prev_block = NULL;
                ctxt->cur_block = block->continuation_block;
                break;
              case JIT_BLOCK_IF:
                gcc_jit_block_end_with_jump (ctxt->cur_block, NULL,
                                             block->continuation_block);
                gcc_jit_block_end_with_jump (block->else_block, NULL,
                                             block->continuation_block);

                if (prev_block && prev_block != ctxt->cur_block)
                gcc_jit_block_end_with_jump (prev_block, NULL, ctxt->cur_block);
                set_prev_block_null = true;
                break;
              case JIT_BLOCK_ELSE:
                if (prev_block && prev_block != ctxt->cur_block)
                  gcc_jit_block_end_with_jump (prev_block, NULL, ctxt->cur_block);

                gcc_jit_block_end_with_jump (ctxt->cur_block, NULL,
                                             block->continuation_block);
                ctxt->cur_block = block->continuation_block;
                prev_block = NULL;
                break;
              case JIT_BLOCK_LOOP:
                {
                  gcc_jit_type *ptr_type =
                    gcc_jit_context_new_function_ptr_type (ctxt->ctxt, NULL,
                                                           ctxt->type_void_ptr,
                                                           0, NULL, 0);
                  gcc_jit_rvalue *fn_ptr_gc =
                    gcc_jit_context_new_rvalue_from_ptr(ctxt->ctxt, ptr_type,
                                                        maybe_gc),
                    *fn_ptr_quit =
                    gcc_jit_context_new_rvalue_from_ptr (ctxt->ctxt, ptr_type,
                                                         maybe_quit),
                    *call1 = gcc_jit_context_new_call_through_ptr (ctxt->ctxt,
                                                                   NULL,
                                                                   fn_ptr_gc,
                                                                   0, NULL),
                    *call2 = gcc_jit_context_new_call_through_ptr (ctxt->ctxt,
                                                                   NULL,
                                                                   fn_ptr_quit,
                                                                   0, NULL);
                  JIT_ADD_COMMENT ("maybe_gc ()");
                  gcc_jit_block_add_eval (ctxt->cur_block, NULL, call1);
                  JIT_ADD_COMMENT ("maybe_quit ()");
                  gcc_jit_block_add_eval (ctxt->cur_block, NULL, call2);

                }
                break;
              default:
                emacs_abort();
              }
            break;
          }

        case Bbr:
          {
            op = FETCH;

            if (op > block_stack->top)
              {
                *error = Qjit_invalid_branch_depth;
                *error_data = list1 (make_fixnum (op));
                return;
              }

            struct jit_block *block = block_stack->stack[block_stack->top - op];
            block->loop_end_block = ctxt->cur_block;
            set_prev_block_null = true;
            break;
          }

          case Bbrif:
            {
              op = FETCH;

              gcc_jit_lvalue *top = var_stack[stack_top--];
              gcc_jit_rvalue *top_is_not_nil =
                  jit_compile_not_NILP (ctxt, gcc_jit_lvalue_as_rvalue (top));
              struct jit_block *block = block_stack->stack[block_stack->top - op];
              gcc_jit_block *block_jump_false =
                  gcc_jit_function_new_block (ctxt->cur_func, "when_false");

              gcc_jit_block_end_with_conditional (ctxt->cur_block, NULL,
                                                  top_is_not_nil,
                                                  block->continuation_block,
                                                  block_jump_false);

              if (prev_block && prev_block != ctxt->cur_block)
                gcc_jit_block_end_with_jump (prev_block, NULL, ctxt->cur_block);

              prev_block = NULL;
              ctxt->cur_block = block_jump_false;
              break;
            }

        case Bloop:
          {
            struct jit_block *block = jit_block_stack_push_loop (ctxt,
                                                                 block_stack);
            gcc_jit_block_end_with_jump (ctxt->cur_block, NULL,
                                         block->continuation_block);
            if (prev_block && prev_block != ctxt->cur_block)
              gcc_jit_block_end_with_jump (prev_block, NULL, ctxt->cur_block);

            prev_block = NULL;
            ctxt->cur_block = block->continuation_block;
            break;
          }

        case Bblock:
          {
            struct jit_block *block =
                jit_block_stack_push_regular_block (ctxt, block_stack);
            /* ctxt->cur_block = block->continuation_block; */
            break;
          }

        case Bconstant2:
          op = FETCH2;
          goto do_constant;

        default:
        case Bconstant:
          {
            if (op < Bconstant || op > Bconstant + vector_size)
              goto fail;
            op -= Bconstant;
          do_constant:

            {
              gcc_jit_rvalue *v1 =
                jit_new_rvalue_from_lisp_object (ctxt, vectorp[op]);
              gcc_jit_lvalue *top = var_stack[++stack_top];
              JIT_ADD_COMMENT (SSDATA (CALLN (Fformat_message,
                                             build_string ("PUSH (%s)"),
                                             vectorp[op])));
              gcc_jit_block_add_assignment (ctxt->cur_block, NULL, top, v1);
            }
            break;
          }

        fail:
          *error = Qjit_invalid_op_error;
          *error_data = list2 (make_fixnum (op),
                               make_fixnum (pc - 1 - bytestr_data));
          return;
        }

      if (prev_block)
        gcc_jit_block_end_with_jump (prev_block, NULL, ctxt->cur_block);

      if (set_prev_block_null)
        prev_block = NULL;
      else
        {
          prev_block = ctxt->cur_block;
          set_prev_block_null = false;
        }
      if (pc < bytestr_data + bytestr_length) {
        sprintf (buf, "instr%ld", pc - 1 - bytestr_data);
        ctxt->cur_block = gcc_jit_function_new_block (ctxt->cur_func, buf);
      }
    }

  gcc_jit_block_add_assignment (scratch_alloc_block, NULL, scratch_local,
                               jit_compile_record_xmalloc (ctxt, lo_ptr_type,
                                                           scratch_max_args));
  gcc_jit_block_end_with_jump (scratch_alloc_block, NULL, first_block);

  if (!NILP (file_dump_name))
    {
      CHECK_STRING (file_dump_name);
      gcc_jit_context_dump_to_file (ctxt->ctxt, (char *)SSDATA (file_dump_name),
                                    1);
    }
  if (!NILP (dot_dump_name))
    {
      CHECK_STRING (dot_dump_name);
      gcc_jit_function_dump_to_dot (ctxt->cur_func,
                                    (char *)SSDATA (dot_dump_name));
    }
  if (!NILP (assembly_name))
    {
      CHECK_STRING (assembly_name);
      gcc_jit_context_compile_to_file (ctxt->ctxt,
                                       GCC_JIT_OUTPUT_KIND_ASSEMBLER,
                                       (char *)SSDATA (assembly_name));
    }
  SAFE_FREE();
}


DEFUN ("jit-compile", Fjit_compile, Sjit_compile, 5, 5, 0,
       doc: /* libgccjit compilation.  */)
     (Lisp_Object func, Lisp_Object dump_file, Lisp_Object dot_dump_file,
      Lisp_Object assembly_output_file, Lisp_Object optimization_level)
{
  if (SYMBOLP (func) && !NILP (func)
      && (func = XSYMBOL (func)->u.s.function, SYMBOLP (func)))
    func = indirect_function (func);

  if (!COMPILEDP (func))
      return Qnil;

  if (!(PVSIZE (func) > COMPILED_JIT_CODE) || !NILP (AREF (func,
                                                           COMPILED_JIT_CODE)))
    error ("invalid byte-code object");

  if (CONSP (AREF (func, COMPILED_BYTECODE)))
    Ffetch_bytecode (func);

  Lisp_Object error = Qnil;
  Lisp_Object error_data = Qnil;

  struct jit_context *ctxt = current_thread->jit_context;
  gcc_jit_context *old_ctxt = ctxt->ctxt;
  struct jit_result *result = xmalloc (sizeof (struct jit_result));

  static char func_name[30];
  sprintf(func_name, "jit_0x%" PRIXPTR "", (uintptr_t)XVECTOR (func));

  ctxt->ctxt = gcc_jit_context_new_child_context (old_ctxt);
  gcc_jit_context_set_bool_allow_unreachable_blocks (ctxt->ctxt, true);
  jit_compile (ctxt, func, func_name, dump_file, dot_dump_file,
               assembly_output_file, optimization_level, result, &error,
               &error_data);

  if (!EQ (error, Qnil))
    {
      xfree (result);
      ctxt->ctxt = old_ctxt;
      xsignal(error, error_data);
    }

  unrequest_sigio ();
  result->result = gcc_jit_context_compile (ctxt->ctxt);
  result->a0 = gcc_jit_result_get_code (result->result, func_name);
  request_sigio ();

  result->ctxt = ctxt->ctxt;
  ASET (func, COMPILED_JIT_CODE, make_mint_ptr (result));
  ctxt->ctxt = old_ctxt;

  return Qnil;
}

/* Simplified version of 'define-error' that works with pure
   objects.  Taken from json.c.  */

static void
define_error (Lisp_Object name, const char *message, Lisp_Object parent)
{
  eassert (SYMBOLP (name));
  eassert (SYMBOLP (parent));
  Lisp_Object parent_conditions = Fget (parent, Qerror_conditions);
  eassert (CONSP (parent_conditions));
  eassert (!NILP (Fmemq (parent, parent_conditions)));
  eassert (NILP (Fmemq (name, parent_conditions)));
  Fput (name, Qerror_conditions, pure_cons (name, parent_conditions));
  Fput (name, Qerror_message, build_pure_c_string (message));
}

void
syms_of_jit (void)
{
  DEFSYM (Qjit_error, "jit-error");
  DEFSYM (Qjit_invalid_op_error, "jit-invalid-op-error");
  DEFSYM (Qjit_invalid_optimization_level, "jit-invalid-optimization-level");
  DEFSYM (Qjit_invalid_branch_depth, "invalid branch depth");
  DEFSYM (Qjit_stack_underflow, "stack underflow");
  DEFSYM (Qjit_stack_overflow, "stack overflow");

  define_error (Qjit_error, "generic JIT error", Qerror);
  define_error (Qjit_invalid_op_error, "invalid op", Qjit_error);
  define_error (Qjit_invalid_optimization_level, "invalid optimization level",
                Qjit_error);
  define_error (Qjit_invalid_branch_depth, "invalid branch depth", Qjit_error);
  define_error (Qjit_stack_underflow, "stack_underflow", Qjit_error);
  define_error (Qjit_stack_overflow, "stack overflow", Qjit_error);


  defsubr (&Sjit_compile);
}
