#ifndef JIT_GCC_H
#define JIT_GCC_H

INLINE_HEADER_BEGIN

#include <config.h>
#include <libgccjit.h>
#include "lisp.h"

struct jit_context;

extern struct jit_context *jit_new_context(void);
extern void syms_of_jit (void);

INLINE_HEADER_END

#endif /* JIT_GCC_H */
