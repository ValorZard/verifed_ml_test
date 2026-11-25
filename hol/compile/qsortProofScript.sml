(*
  End-to-end correctness: compose
    - the semantics theorem for the generated program (qsortProg),
    - the CakeML compiler correctness theorem (backendProof.compile_correct),
    - the in-logic compilation result (qsortCompile),
  to get a theorem about the behaviour of the x64 machine code in qsort.S.
*)
Theory qsortProof
Ancestors
  semanticsProps backendProof x64_configProof qsortProg qsortCompile
Libs
  preamble

val qsort_terminate = UNDISCH_ALL qsort_semantics
  |> SIMP_RULE bool_ss [RIGHT_EXISTS_AND_THM]
  |> HO_MATCH_MP ml_progTheory.sem_satisfies_IMP_Terminate
  |> SRULE [qsort_compiled];

Theorem qsort_compiled_thm =
  MATCH_MP compile_correct (cj 1 qsort_compiled)
  |> SIMP_RULE(srw_ss())[LET_THM,ml_progTheory.init_state_env_thm,GSYM AND_IMP_INTRO]
  |> C MATCH_MP (cj 1 qsort_terminate)
  |> C MATCH_MP x64_backend_config_ok
  |> Q.GEN ‘mc’ |> ISPEC (x64_init_ok |> concl |> rand |> rand) |> UNDISCH_ALL
  |> MATCH_MP (cj 2 qsort_terminate)
  |> REWRITE_RULE [targetPropsTheory.machine_sem_sing] |> DISCH_ALL
  |> CONJ (UNDISCH is_x64_machine_config_IMP)
  |> SRULE [SF CONJ_ss] |> CONJUNCT2 |> DISCH_ALL
  |> REWRITE_RULE [AND_IMP_INTRO, GSYM CONJ_ASSOC]
  |> check_thm
