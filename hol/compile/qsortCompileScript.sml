(*
  Compile the generated CakeML program to x64 machine code by evaluation
  inside the logic of HOL4 (using the verified CakeML compiler definition).
  This produces qsort.S and a theorem stating which bytes/data were produced.
*)
Theory qsortCompile
Ancestors
  qsortProg
Libs
  preamble eval_cake_compile_x64Lib

Theorem qsort_compiled =
  eval_cake_compile_x64 "" qsort_prog_def "qsort.S";
