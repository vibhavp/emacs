;;  -*- lexical-binding: t -*-

(require 'bytecomp)

(defun factorial (n)
  (let ((fac 1))
    (dotimes (i n)
      (setq fac (* fac (1+ i))))
    fac))

(let ((byte-compile-emit-ir t)
      (byte-optimize nil)
      (tmp-file "jit-repr")
      (asm-file "jit-asm")
      (dot-file "jit-dot.dot"))
  (byte-compile 'factorial)
  (jit-compile 'factorial tmp-file dot-file asm-file 3))

(message "%d" (factorial 100))
