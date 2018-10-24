#ifndef JIT_GCC_H
#define JIT_GCC_H

INLINE_HEADER_BEGIN

#include <config.h>
#include <libgccjit.h>
#include "lisp.h"

struct jit_block_stack;

struct jit_context
{
  gcc_jit_context *ctxt;

  gcc_jit_type *type_lisp_type;
  gcc_jit_type *type_emacs_int;
  gcc_jit_type *type_emacs_uint;
  gcc_jit_type *type_lisp_word;

  gcc_jit_type *type_intptr_t;
  gcc_jit_type *type_char_ptr;
  gcc_jit_type *type_void_ptr;
  gcc_jit_type *type_void;
  gcc_jit_type *type_ptrdiff_t;
  gcc_jit_type *type_bool;

  gcc_jit_struct *struct_lisp_object;

  gcc_jit_type *type_lisp_object;
  gcc_jit_field *field_lisp_object;

  gcc_jit_rvalue *rvalue_nil;
  gcc_jit_rvalue *rvalue_t;

  gcc_jit_block *cur_block;
  gcc_jit_function *cur_func;
  size_t local_index;

  struct jit_block_stack *block_stack;
};

extern struct jit_context *jit_new_context(void);
extern void syms_of_jit (void);

INLINE_HEADER_END

#endif /* JIT_GCC_H */
