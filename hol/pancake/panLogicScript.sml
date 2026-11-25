(*
  A small program logic for Pancake, proved sound with respect to the
  official functional big-step semantics panSem$evaluate.

    runs p s P   means: for some amount of extra clock, running p from s
                 produces a (result, state) pair satisfying P.

  P is a predicate on the outcome, so the rules compose in continuation-
  passing (weakest-precondition) style: the postcondition of the first half
  of a Seq is "running the second half establishes P".

  fun_spec captures the meaning of a function contract (requires/ensures).
*)
Theory panLogic
Ancestors
  panLang panSem panProps
Libs
  preamble

(* ------------------------------------------------------------------------
   The judgement
   ------------------------------------------------------------------------ *)

Definition runs_def:
  runs p (s:('a,'ffi) panSem$state) P ⇔
    ∃ck. P (evaluate (p, s with clock := s.clock + ck))
End

(* The parts of the state that a function body never changes. *)
Definition same_frame_def:
  same_frame (s0:('a,'ffi) panSem$state) s ⇔
    s.code = s0.code ∧ s.memaddrs = s0.memaddrs ∧ s.be = s0.be ∧
    s.base_addr = s0.base_addr ∧ s.top_addr = s0.top_addr ∧
    s.globals = s0.globals ∧ s.eshapes = s0.eshapes ∧
    s.structs = s0.structs ∧ s.sh_memaddrs = s0.sh_memaddrs
End

(* The word value of local variable x (used in loop variants). *)
Definition lv_def:
  lv (s:('a,'ffi) panSem$state) x =
    case FLOOKUP s.locals x of SOME (Val (Word w)) => w | _ => 0w
End

Theorem with_clock_self[local,simp]:
  (s:('a,'ffi) panSem$state) with clock := s.clock = s
Proof
  simp[state_component_equality]
QED

Theorem runs_eval:
  P (evaluate (p, s)) ⇒ runs p s P
Proof
  rw[runs_def] >> qexists_tac ‘0’ >> simp[]
QED

Theorem runs_mono:
  runs p s P ∧ (∀x. P x ⇒ Q x) ⇒ runs p s Q
Proof
  rw[runs_def] >> metis_tac[]
QED

(* ------------------------------------------------------------------------
   Structural rules
   ------------------------------------------------------------------------ *)

Theorem runs_Seq:
  runs p1 s (λ(r,t). if r = NONE then runs p2 t P else P (r,t)) ⇒
  runs (Seq p1 p2) s P
Proof
  rw[runs_def] >>
  Cases_on ‘evaluate (p1, s with clock := s.clock + ck)’ >> gvs[] >>
  Cases_on ‘q = NONE’ >> gvs[]
  >- (qexists_tac ‘ck + ck'’ >> simp[evaluate_def] >>
      drule evaluate_add_clock_eq >> simp[] >>
      disch_then (qspec_then ‘ck'’ mp_tac) >> simp[])
  >- (qexists_tac ‘ck’ >> simp[evaluate_def])
QED

Theorem runs_Dec:
  eval s e = SOME v ∧ shape_of v = sh ∧
  runs p (s with locals := s.locals |+ (x,v))
    (λ(r,t). P (r, t with locals := res_var t.locals (x, FLOOKUP s.locals x))) ⇒
  runs (Dec x sh e p) s P
Proof
  rw[runs_def] >> qexists_tac ‘ck’ >>
  simp[evaluate_def, eval_upd_clock_eq] >>
  Cases_on ‘evaluate (p, s with <|locals := s.locals |+ (x,v); clock := ck + s.clock|>)’ >>
  gvs[]
QED

Theorem runs_If:
  eval s e = SOME (ValWord w) ∧ runs (if w ≠ 0w then c1 else c2) s P ⇒
  runs (If e c1 c2) s P
Proof
  rw[runs_def] >> qexists_tac ‘ck’ >> simp[evaluate_def, eval_upd_clock_eq]
QED

(* Loop rule: an invariant Inv (indexed by ghost state g) and a variant μ. *)
Theorem runs_While:
  ∀(Inv: 'g -> ('a,'ffi) panSem$state -> bool) μ P e c.
    (∀g s. Inv g s ⇒
       ∃w. eval s e = SOME (ValWord w) ∧
           (w = 0w ⇒ P (NONE, s)) ∧
           (w ≠ 0w ⇒
              runs c s (λ(r,t).
                 if r = NONE ∨ r = SOME Continue then
                   ∃g'. Inv g' t ∧ μ g' t < (μ g s : num)
                 else if r = SOME Break then P (NONE, t)
                 else P (r, t)))) ⇒
    ∀g s. Inv g s ⇒ runs (While e c) s P
Proof
  rpt gen_tac >> strip_tac >>
  ‘∀n g s. μ g s = n ∧ Inv g s ⇒ runs (While e c) s P’
    suffices_by metis_tac[] >>
  completeInduct_on ‘n’ >> rw[] >>
  first_assum drule >> strip_tac >>
  Cases_on ‘w = 0w’ >> gvs[]
  >- (irule runs_eval >> simp[Once evaluate_def]) >>
  qpat_x_assum ‘runs c _ _’ (strip_assume_tac o REWRITE_RULE [runs_def]) >>
  simp[runs_def] >>
  Cases_on ‘evaluate (c,s with clock := s.clock + ck)’ >> fs[] >>
  Cases_on ‘q = NONE ∨ q = SOME Continue’ >> fs[] >>
  TRY (first_x_assum (qspec_then ‘μ g' r’ mp_tac) >> impl_tac >- simp[] >>
       disch_then (qspecl_then [‘g'’,‘r’] mp_tac) >> simp[runs_def] >>
       strip_tac >> qexists_tac ‘ck + ck' + 1’ >>
       simp[Once evaluate_def, eval_upd_clock_eq, dec_clock_def] >>
       drule evaluate_add_clock_eq >> simp[] >>
       disch_then (qspec_then ‘ck'’ mp_tac) >> simp[] >> NO_TAC) >>
  qexists_tac ‘ck + 1’ >>
  simp[Once evaluate_def, eval_upd_clock_eq, dec_clock_def] >>
  Cases_on ‘q’ >> fs[] >> Cases_on ‘x’ >> fs[]
QED

(* The loop rule in the form used by tactics (free variables of Inv stay fixed). *)
Theorem runs_While_inv:
  ∀(Inv: 'g -> ('a,'ffi) panSem$state -> bool) μ P e c s.
    (∀g s. Inv g s ⇒
       ∃w. eval s e = SOME (ValWord w) ∧
           (w = 0w ⇒ P (NONE, s)) ∧
           (w ≠ 0w ⇒
              runs c s (λ(r,t).
                 if r = NONE ∨ r = SOME Continue then
                   ∃g'. Inv g' t ∧ μ g' t < (μ g s : num)
                 else if r = SOME Break then P (NONE, t)
                 else P (r, t)))) ∧
    (∃g. Inv g s) ⇒
    runs (While e c) s P
Proof
  metis_tac[runs_While]
QED

(* ------------------------------------------------------------------------
   Function contracts
   ------------------------------------------------------------------------ *)

(* Function fname has word parameters params and a word result.  For all
   calls whose arguments vs satisfy the precondition P, the body returns a
   word v, changes at most memory and FFI state (locals are discarded on
   return), and the postcondition Q relates the call state s, the result v,
   and the final memory and FFI state. *)
Definition fun_spec_def:
  fun_spec code fname (params: mlstring list)
           (P: 'a word list -> ('a,'ffi) panSem$state -> bool)
           (Q: 'a word list -> ('a,'ffi) panSem$state -> 'a word ->
               ('a word -> 'a word_lab) -> 'ffi ffi_state -> bool) ⇔
    ∃body.
      FLOOKUP code fname = SOME (MAP (λp. (p, One)) params, body, One) ∧
      ALL_DISTINCT params ∧
      ∀s vs.
        s.code = code ∧ LENGTH vs = LENGTH params ∧ P vs s ⇒
        runs body (s with locals := FEMPTY |++ ZIP (params, MAP ValWord vs))
          (λ(r,t). ∃v. r = SOME (Return (ValWord v)) ∧
                       t = s with <| locals := FEMPTY; memory := t.memory;
                                     ffi := t.ffi; clock := t.clock |> ∧
                       Q vs s v t.memory t.ffi)
End

Theorem OPT_MMAP_MAP_ValWord[local]:
  ∀vs. LIST_REL (λvshape arg. SND vshape = shape_of arg)
                (MAP (λp. (p,One)) params) (MAP ValWord vs) ⇔
       LENGTH vs = LENGTH params
Proof
  Induct_on ‘params’ >> rw[] >> Cases_on ‘vs’ >> gvs[shape_of_def]
QED

Theorem fun_spec_lookup[local]:
  fun_spec code f params P Q ∧ LENGTH vs = LENGTH params ⇒
  ∃body. lookup_code code f (MAP ValWord vs) =
           SOME (body, FEMPTY |++ ZIP (params, MAP ValWord vs), One) ∧
         ∀s. s.code = code ∧ P vs s ⇒
           runs body (s with locals := FEMPTY |++ ZIP (params, MAP ValWord vs))
             (λ(r,t). ∃v. r = SOME (Return (ValWord v)) ∧
                          t = s with <| locals := FEMPTY; memory := t.memory;
                                        ffi := t.ffi; clock := t.clock |> ∧
                          Q vs s v t.memory t.ffi)
Proof
  rw[fun_spec_def] >> qexists_tac ‘body’ >>
  simp[lookup_code_def, OPT_MMAP_MAP_ValWord, MAP_MAP_o, combinTheory.o_DEF]
QED

(* Tail call  `return f(args);` *)
Theorem runs_TailCall_spec:
  fun_spec s.code f params Pre Post ∧
  OPT_MMAP (eval s) args = SOME (MAP ValWord vs) ∧
  LENGTH vs = LENGTH params ∧ Pre vs s ∧
  (∀v m ff c. Post vs s v m ff ⇒
     P (SOME (Return (ValWord v)),
        s with <| locals := FEMPTY; memory := m; ffi := ff; clock := c |>)) ⇒
  runs (Call NONE f args) s P
Proof
  strip_tac >> drule_all fun_spec_lookup >> strip_tac >>
  first_x_assum (qspec_then ‘s’ mp_tac) >> simp[] >>
  rw[runs_def] >> qexists_tac ‘ck + 1’ >>
  simp[evaluate_def, opt_mmap_eval_upd_clock_eq, dec_clock_def] >>
  pairarg_tac >> fs[] >> gvs[shape_of_def, empty_locals_def] >>
  qpat_x_assum ‘∀v m ff c. _’ (drule_then (qspec_then ‘t.clock’ mp_tac)) >>
  qpat_x_assum ‘t = _’ (fn th => ONCE_REWRITE_TAC [th]) >> simp[]
QED

(* Stand-alone call  `f(args);`  (result discarded) *)
Theorem runs_StandAloneCall_spec:
  fun_spec s.code f params Pre Post ∧
  OPT_MMAP (eval s) args = SOME (MAP ValWord vs) ∧
  LENGTH vs = LENGTH params ∧ Pre vs s ∧
  (∀v m ff c. Post vs s v m ff ⇒
     P (NONE, s with <| memory := m; ffi := ff; clock := c |>)) ⇒
  runs (Call (SOME (NONE, h)) f args) s P
Proof
  strip_tac >> drule_all fun_spec_lookup >> strip_tac >>
  first_x_assum (qspec_then ‘s’ mp_tac) >> simp[] >>
  rw[runs_def] >> qexists_tac ‘ck + 1’ >>
  simp[evaluate_def, opt_mmap_eval_upd_clock_eq, dec_clock_def] >>
  pairarg_tac >> fs[] >> gvs[shape_of_def, empty_locals_def] >>
  qpat_x_assum ‘∀v m ff c. _’ (drule_then (qspec_then ‘t.clock’ mp_tac)) >>
  qpat_x_assum ‘t = _’ (fn th => ONCE_REWRITE_TAC [th]) >> simp[] >>
  strip_tac >> qmatch_goalsub_abbrev_tac ‘P (NONE, X)’ >>
  ‘X = s with <|memory := t.memory; clock := t.clock; ffi := t.ffi|>’
    by simp[Abbr ‘X’, state_component_equality] >>
  fs[]
QED

(* Declaring call  `var 1 x = f(args); p1` *)
Theorem runs_DecCall_spec:
  fun_spec s.code f params Pre Post ∧
  OPT_MMAP (eval s) args = SOME (MAP ValWord vs) ∧
  LENGTH vs = LENGTH params ∧ Pre vs s ∧
  (∀v m ff c. Post vs s v m ff ⇒
     runs p1 (s with <| locals := s.locals |+ (x, ValWord v);
                        memory := m; ffi := ff; clock := c |>)
       (λ(r,t). P (r, t with locals := res_var t.locals (x, FLOOKUP s.locals x)))) ⇒
  runs (DecCall x One f args p1) s P
Proof
  strip_tac >> drule_all fun_spec_lookup >> strip_tac >>
  first_x_assum (qspec_then ‘s’ mp_tac) >> simp[] >>
  simp[runs_def] >> strip_tac >> pairarg_tac >> gvs[] >>
  qpat_x_assum ‘∀v m ff c. _’ (drule_then (qspec_then ‘t.clock’ mp_tac)) >>
  simp[runs_def] >> strip_tac >>
  qexists_tac ‘ck + ck' + 1’ >>
  simp[evaluate_def, opt_mmap_eval_upd_clock_eq, dec_clock_def] >>
  qpat_x_assum ‘evaluate (body, _) = _’
    (mp_then Any (qspec_then ‘ck'’ mp_tac) evaluate_add_clock_eq) >>
  simp[shape_of_def, set_var_def] >>
  strip_tac >> qmatch_goalsub_abbrev_tac ‘evaluate (p1, X)’ >>
  qmatch_asmsub_abbrev_tac ‘evaluate (p1, Y)’ >>
  ‘X = Y’ by (unabbrev_all_tac >>
              qpat_x_assum ‘t = _’ (fn th => ONCE_REWRITE_TAC [th]) >>
              simp[state_component_equality]) >>
  pop_assum SUBST_ALL_TAC >>
  Cases_on ‘evaluate (p1, Y)’ >> fs[]
QED

(* ------------------------------------------------------------------------
   From a specification of main to the observable semantics
   ------------------------------------------------------------------------ *)

Theorem runs_semantics:
  runs (Call NONE start []) s
    (λ(r,t). (∃v. r = SOME (Return v)) ∧ t.ffi.io_events = evs) ⇒
  semantics s start = Terminate Success evs
Proof
  rw[runs_def] >>
  Cases_on ‘evaluate (Call NONE start [],s with clock := ck + s.clock)’ >> gvs[] >>
  sg ‘∀k r' t'. evaluate (Call NONE start [], s with clock := k) = (r',t') ∧
                r' ≠ SOME TimeOut ⇒ r' = SOME (Return v) ∧ t'.ffi = r.ffi’
  >- (rpt gen_tac >> strip_tac >> drule evaluate_add_clock_eq >> simp[] >>
      disch_then (qspec_then ‘ck + s.clock’ mp_tac) >>
      qpat_x_assum ‘evaluate _ = (SOME (Return v), r)’
        (mp_then Any (qspec_then ‘k’ mp_tac) evaluate_add_clock_eq) >>
      simp[] >> rpt strip_tac >> gvs[state_component_equality]) >>
  simp[semantics_def] >> IF_CASES_TAC
  >- (gvs[] >>
      Cases_on ‘evaluate (Call NONE start [], s with clock := k)’ >> gvs[] >>
      Cases_on ‘q = SOME TimeOut’ >> gvs[] >>
      qpat_x_assum ‘∀k r' t'. _’ drule >> simp[] >> strip_tac >> gvs[]) >>
  DEEP_INTRO_TAC some_intro >> rw[]
  >- (Cases_on ‘r' = SOME TimeOut’ >> gvs[] >>
      qpat_x_assum ‘∀k r' t'. _’ drule >> simp[] >> strip_tac >> gvs[])
  >- (qexistsl_tac [‘ck + s.clock’, ‘r’, ‘SOME (Return v)’] >> simp[])
QED
