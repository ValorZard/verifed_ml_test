(*
  Generate a complete CakeML program from the HOL4 definitions, and prove
  what it does.

  Nothing here is written in CakeML: the pure functions are translated by
  CakeML's proof-producing translator (`translate`), and the effectful main
  function is a HOL4 function in a state/IO monad that is translated by the
  monadic translator (`m_translate`).  The top-level call `main ()` is added
  by `prove_sem_thm`.  The result is the deeply embedded CakeML program
  `qsort_prog` together with a theorem about its observable behaviour.
*)
Theory qsortProg
Ancestors
  qsort basisProg ml_monad_translator cfMonad basis_ffi
  CommandLineProof TextIOProof
Libs
  preamble basis ml_monad_translator_interfaceLib cfMonadLib
  astToSexprLib

val _ = set_up_monadic_translator ();
val _ = translation_extends "basisProg";

(* ------------------------------------------------------------------------
   Pure part: parsing the arguments and printing the result
   ------------------------------------------------------------------------ *)

(* Every command-line argument must be an integer (e.g. 42, -7, ~7, +3). *)
Definition parse_ints_def:
  parse_ints [] = SOME [] ∧
  parse_ints (s::ss) =
    case mlint$fromString s of
      NONE => NONE
    | SOME (i:int) =>
        (case parse_ints ss of
           NONE => NONE
         | SOME is => SOME (i::is))
End

(* One integer per line, negative numbers written with a leading "-". *)
Definition show_ints_def:
  show_ints (is:int list) =
    concat (MAP (λi. mlint$int_to_string #"-" i ^ «\n») is)
End

Definition valid_args_def:
  valid_args args = case parse_ints args of NONE => F | SOME _ => T
End

Definition sorted_output_def:
  sorted_output args =
    case parse_ints args of
      NONE => «»
    | SOME ns => show_ints (qsort ns)
End

Definition usage_msg_def:
  usage_msg = «usage: qsort <int> <int> ...  (every argument must be an integer)\n»
End

val r = translate parse_ints_def;
val r = translate show_ints_def;
val r = translate qsort_def;
val r = translate valid_args_def;
val r = translate sorted_output_def;
val r = translate usage_msg_def;

(* ------------------------------------------------------------------------
   Effectful part: main, as a HOL function in a state monad whose state
   holds the command line and the (model of the) file system / stdio
   ------------------------------------------------------------------------ *)

Datatype:
  state_refs = <| commandline : mlstring list ; stdio : IO_fs |>
End

val config = global_state_config |>
             with_state ``:state_refs`` |>
             with_commandline "commandline" "stdio";

val _ = start_translation config;

Definition qsort_main_def:
  qsort_main (u:unit) =
    (do
       args <- commandline (arguments ());
       if valid_args args then
         stdio (print (sorted_output args))
       else
         stdio (print_err usage_msg)
     od) : (state_refs, unit, unit) M
End

val qsort_main_v_thm = m_translate qsort_main_def;

Theorem qsort_main_app = cfMonadLib.mk_app_of_ArrowP qsort_main_v_thm |> SPEC_ALL;

(* ------------------------------------------------------------------------
   Specification of the whole program
   ------------------------------------------------------------------------ *)

(* The file system after running the program on command line cl. *)
Definition qsort_result_def:
  qsort_result cl fs =
    if valid_args (TL cl) then add_stdout fs (sorted_output (TL cl))
    else add_stderr fs usage_msg
End

val st = get_ml_prog_state ();
val qsort_main_v = fetch_v "qsort_main" st;

Theorem POSTve_POSTv[local]:
  ∀Q. POSTve Q (λx. SEP_F) = $POSTv Q
Proof
  rw [SEP_CLAUSES, POSTv_def, POSTve_def]
QED

(* What the HOL main function does to the monadic state. *)
Theorem qsort_main_run[local]:
  qsort_main () <|commandline := cl; stdio := fs|> =
    (M_success (), <|commandline := cl; stdio := qsort_result cl fs|>)
Proof
  rw[qsort_main_def, arguments_def, print_def, print_err_def,
     ml_monadBaseTheory.st_ex_bind_def, ml_monadBaseTheory.liftM_def,
     qsort_result_def]
QED

(* The translator's result for main, specialised to a concrete command line
   and file system.  The exception branch is impossible: main never raises. *)
val main_app =
  qsort_main_app
  |> Q.INST [‘x1’ |-> ‘()’, ‘xv1’ |-> ‘Conv NONE []’,
             ‘state’ |-> ‘<|commandline := cl; stdio := fs|>’]
  |> SIMP_RULE (srw_ss()) [UNIT_TYPE_def]
  |> REWRITE_RULE [qsort_main_run]
  |> SIMP_RULE (srw_ss()) [fetch "-" "STATE_REFS_def", MONAD_IO_def, SEP_CLAUSES,
                           POSTve_POSTv];

(* CF specification of the generated main function. *)
Theorem qsort_main_spec:
  hasFreeFD fs ⇒
  app (p:'ffi ffi_proj) ^qsort_main_v [Conv NONE []]
    (COMMANDLINE cl * STDIO fs)
    (POSTv uv. &UNIT_TYPE () uv * COMMANDLINE cl * STDIO (qsort_result cl fs))
Proof
  strip_tac >>
  match_mp_tac (MP_CANON (MATCH_MP app_wgframe main_app)) >>
  xsimpl >> fs[]
QED

Theorem qsort_whole_prog_spec:
  hasFreeFD fs ⇒
  whole_prog_spec ^qsort_main_v cl fs NONE ((=) (qsort_result cl fs))
Proof
  strip_tac >>
  simp_tac bool_ss [whole_prog_spec_def] >>
  qexists_tac ‘qsort_result cl fs’ >> conj_tac
  >- (irule app_wgframe >> irule_at Any qsort_main_spec >> simp[] >>
      xsimpl >> qexistsl_tac [‘fs’, ‘cl’, ‘emp’] >> gvs[] >> xsimpl)
  >- (rw[qsort_result_def] >>
      simp[GSYM add_stdo_with_numchars, with_same_numchars])
QED

(* Adds the top-level call `main ()`, defines the complete deeply embedded
   program qsort_prog, and proves its semantics from the spec above. *)
Theorem qsort_semantics =
  prove_sem_thm "qsort_main" "qsort_prog" qsort_whole_prog_spec;

val qsort_prog_def = definition "qsort_prog_def";

(* ------------------------------------------------------------------------
   The headline theorem.

   For any command line cl and any well-formed initial file system fs, every
   behaviour of the CakeML program qsort_prog terminates successfully, and
   the resulting file system fs' (as observed through the FFI events) is:
     - if every argument is an integer (ns = the parsed arguments):
         fs with  show_ints ys  appended to stdout,
         where ys is sorted (≤) and a permutation of ns;
     - otherwise: fs with the usage message appended to stderr.
   ------------------------------------------------------------------------ *)

Theorem qsort_prog_correct:
  hasFreeFD fs ∧ wfcl cl ∧ wfFS fs ∧ STD_streams fs ⇒
  sem_satisfies
    (semantics_dec_list (init_state (basis_ffi ext cl fs)) init_env qsort_prog)
    (λbehaviour.
       ∃io_events fs'.
         behaviour = Terminate Success io_events ∧
         extract_fs ext (cl,fs) io_events = SOME fs' ∧
         case parse_ints (TL cl) of
           SOME ns =>
             ∃ys. SORTED $<= ys ∧ PERM ys ns ∧
                  fs' = add_stdout fs (show_ints ys)
         | NONE => fs' = add_stderr fs usage_msg)
Proof
  strip_tac >> drule_all qsort_semantics >>
  rw[semanticsPropsTheory.sem_satisfies_def] >>
  first_x_assum (qspec_then ‘ext’ strip_assume_tac) >>
  first_x_assum drule >> rw[] >>
  simp[qsort_result_def, valid_args_def, sorted_output_def] >>
  every_case_tac >> gvs[] >>
  metis_tac[qsort_SORTED, qsort_PERM]
QED

(* ------------------------------------------------------------------------
   Write the generated CakeML program out as an S-expression, so that the
   (verified, bootstrapped) CakeML compiler binary can compile it.
   ------------------------------------------------------------------------ *)

val _ = astToSexprLib.write_program_def_to_file "qsort.sexp" qsort_prog_def;
