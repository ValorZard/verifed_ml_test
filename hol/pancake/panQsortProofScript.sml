(*
  Proofs of the contracts written in qsort.pnk.

  Each proof obligation is generated from the contract annotations by
  panContractLib (fun_spec_goal); the proofs use the program logic of
  panLogic and the symbolic-execution tactics of panStepLib.
*)
Theory panQsortProof
Ancestors
  panQsortProg panQsortSpec panLogic panSem panLang byte misc ffi
Libs
  preamble panContractLib panStepLib

val decls = rhs (concl qsort_decls_def);
val contracts = panContractLib.contracts_of decls;
fun goal_of name =
  panContractLib.fun_spec_goal “qsort_code” (find_contract contracts name);
val st = “s : (64, word64 list) panSem$state”;
fun loop name i =
  panStepLib.loop_contract_at
    (List.nth (#loops (find_contract contracts name), i)) st;

(* ------------------------------------------------------------------------
   Lemmas about list segments
   ------------------------------------------------------------------------ *)

Theorem lseg_update:
  ∀xs m p q x y. lseg m xs p q ∧ EVERY (λa. x ≠ a ∧ x ≠ a + 8w) (MAP FST xs) ⇒
                 lseg ((x =+ y) m) xs p q
Proof
  Induct >> simp[lseg_def, pairTheory.FORALL_PROD, combinTheory.APPLY_UPDATE_THM] >>
  rw[] >> metis_tac[]
QED

Theorem lseg_null:
  ∀xs m p. lseg m xs p 0w ∧ EVERY (λa. a ≠ 0w) (MAP FST xs) ⇒ (p = 0w ⇔ xs = [])
Proof
  Cases >> simp[lseg_def, pairTheory.FORALL_PROD] >>
  Cases_on ‘h’ >> simp[lseg_def] >> rw[] >> gvs[]
QED

(* ------------------------------------------------------------------------
   FFI buffer lemmas in rewrite-friendly form
   ------------------------------------------------------------------------ *)

Theorem read_bytearray_word':
  aligned 3 (a:word64) ∧ a ∈ dm ⇒
  read_bytearray a 8 (mem_load_byte m dm F) =
    SOME (word_to_bytes (theWord (m a)) F)
Proof
  strip_tac >> irule read_bytearray_word >> simp[] >>
  Cases_on ‘m a’ >> simp[theWord_def]
QED

Theorem write_bytearray_word':
  aligned 3 (a:word64) ∧ a ∈ dm ⇒
  write_bytearray a (word_to_bytes w F) m dm F = (a =+ Word w) m
Proof
  strip_tac >> drule_all write_bytearray_word >>
  disch_then (qspecl_then [‘w’, ‘[]’, ‘m’] mp_tac) >>
  simp[write_bytearray_def]
QED

val ffi_thms =
  [read_bytearray_word', write_bytearray_word', write_bytearray_word,
   call_FFI_def, qs_oracle_def, LENGTH_word_to_bytes, read_bytearray_def,
   theWord_def, combinTheory.UPDATE_EQ, LET_THM];

(* ------------------------------------------------------------------------
   print_list
   ------------------------------------------------------------------------ *)

val print_list_spec = store_thm ("print_list_spec", goal_of "print_list",
  rpt gen_tac >> simp[fun_spec_def, qsort_code_lookups] >>
  rpt strip_tac >> gvs[] >>
  rewrite_tac [print_list_body_def] >> steps_tac >>
  (let val (inv, var) = loop "print_list" 0 in while_tac inv var end)
  >- (
    simp[pairTheory.FORALL_PROD] >> rpt gen_tac >> strip_tac >>
    gvs[same_frame_def] >> simp eval_simps >> conj_tac
    >- ((* loop exit: l = 0, so the rest of the list is empty *)
        rw[] >>
        ‘p_2 = []’ by (drule lseg_null >> impl_tac
                       >- (gvs[nodes_ok_def, listTheory.EVERY_MEM] >> metis_tac[]) >>
                       simp[]) >>
        gvs[] >> steps_with i2w_simps >>
        gvs[state_component_equality])
    >- ((* one iteration: print the head node, move to the next *)
        rw[] >> Cases_on ‘p_2’ >- gvs[lseg_def] >>
        PairCases_on ‘h’ >> gvs[lseg_def] >>
        rename1 ‘s'.memory (h0 + 8w) = Word nxt’ >>
        rename1 ‘lseg s'.memory rest nxt 0w’ >>
        ‘h0 ∈ s.memaddrs ∧ h0 + 8w ∈ s.memaddrs ∧ h0 ≠ 0w ∧
         away_from s.base_addr h0’
          by (gvs[nodes_ok_def] >> metis_tac[]) >>
        ‘s.base_addr ≠ h0 + 8w ∧ s.memory (h0 + 8w) = Word nxt’
          by (gvs[away_from_def] >> metis_tac[]) >>
        steps_with ffi_thms >>
        asimp (eval_simps @ ffi_thms) >>
        qexists_tac ‘(p_1 ++ [(h0,h1)], rest)’ >>
        simp[finite_mapTheory.FLOOKUP_UPDATE, put_ev_def,
             combinTheory.APPLY_UPDATE_THM, ffi_state_component_equality] >>
        irule lseg_update >> gvs[listTheory.EVERY_MEM, away_from_def] >>
        metis_tac[]))
  >- (qexists_tac ‘([], ys)’ >>
      simp[same_frame_def, finite_mapTheory.FLOOKUP_UPDATE]));

(* ------------------------------------------------------------------------
   Node allocation (read_list)
   ------------------------------------------------------------------------ *)

Theorem base_add_11:
  w2n (base:word64) + i < dimword(:64) ∧ w2n base + j < dimword(:64) ⇒
  (base + n2w i = base + n2w j ⇔ i = j)
Proof
  rw[] >> eq_tac >> rw[] >>
  ‘w2n (base + n2w i) = w2n (base + n2w j)’ by simp[] >>
  gvs[wordsTheory.word_add_def, wordsTheory.w2n_n2w]
QED

Theorem w2n_base_add:
  w2n (base:word64) + j < dimword(:64) ⇒ w2n (base + n2w j) = w2n base + j
Proof
  rw[wordsTheory.word_add_def, wordsTheory.w2n_n2w]
QED

Theorem node_plus_8:
  (base:word64) + n2w (16 * i + 16) + 8w = base + n2w (16 * i + 24)
Proof
  REWRITE_TAC [GSYM wordsTheory.WORD_ADD_ASSOC, wordsTheory.word_add_n2w] >> simp[]
QED

Theorem n2w_plus_8:
  n2w x + (base:word64) + 8w = n2w (x + 8) + base
Proof
  ‘n2w (x + 8) = n2w x + (8w:word64)’ by REWRITE_TAC [wordsTheory.word_add_n2w] >>
  pop_assum SUBST1_TAC >>
  metis_tac[wordsTheory.WORD_ADD_COMM, wordsTheory.WORD_ADD_ASSOC]
QED

Theorem heap_form:
  n2w (16 * k) + (base:word64) + 16w = base + n2w (16 * k + 16)
Proof
  ‘n2w (16 * k + 16) = n2w (16 * k) + (16w:word64)’
    by REWRITE_TAC [wordsTheory.word_add_n2w] >>
  pop_assum SUBST1_TAC >>
  metis_tac[wordsTheory.WORD_ADD_COMM, wordsTheory.WORD_ADD_ASSOC]
QED

Theorem ne_plus_8:
  (a:word64) ≠ a + 8w ∧ a + 8w ≠ a
Proof
  blastLib.BBLAST_TAC
QED

Theorem alloc_list_nil:
  alloc_list base [] = []
Proof
  simp[alloc_list_def]
QED

Theorem alloc_list_snoc:
  alloc_list base (ds ++ [w]) =
    (base + n2w (16 * LENGTH ds + 16), w) :: alloc_list base ds
Proof
  simp[alloc_list_def, indexedListsTheory.MAPi_APPEND] >>
  REWRITE_TAC [GSYM wordsTheory.WORD_ADD_ASSOC, wordsTheory.word_add_n2w]
QED

Theorem MAP_SND_alloc_list:
  MAP SND (alloc_list base ds) = REVERSE ds
Proof
  simp[alloc_list_def, listTheory.MAP_REVERSE, indexedListsTheory.MAP_MAPi] >>
  simp[combinTheory.o_DEF, indexedListsTheory.MAPi_GENLIST] >>
  simp[listTheory.LIST_EQ_REWRITE]
QED

Theorem MEM_alloc_list:
  ∀ds a. MEM a (MAP FST (alloc_list base ds)) ⇔
         ∃i. i < LENGTH ds ∧ a = base + n2w (16 * i + 16)
Proof
  ho_match_mp_tac listTheory.SNOC_INDUCT >>
  rw[alloc_list_nil, listTheory.SNOC_APPEND, alloc_list_snoc] >>
  eq_tac >> rw[]
  >- (qexists_tac ‘LENGTH ds’ >> simp[])
  >- (qexists_tac ‘i’ >> simp[])
  >- (Cases_on ‘i = LENGTH ds’ >> gvs[] >> disj2_tac >> qexists_tac ‘i’ >> simp[])
QED

Theorem alloc_list_distinct:
  ∀ds. w2n (base:word64) + 16 * LENGTH ds < dimword(:64) ⇒
       ALL_DISTINCT (MAP FST (alloc_list base ds))
Proof
  ho_match_mp_tac listTheory.SNOC_INDUCT >>
  rw[alloc_list_nil, listTheory.SNOC_APPEND, alloc_list_snoc, MEM_alloc_list] >>
  rw[] >> CCONTR_TAC >> gvs[] >>
  qpat_x_assum ‘_ = _’ mp_tac >> simp[base_add_11]
QED

Theorem alloc_list_ok:
  heap_ok base tp dm n ∧ LENGTH ds ≤ n ⇒
  nodes_ok dm (MAP FST (alloc_list base ds)) ∧
  EVERY (away_from base) (MAP FST (alloc_list base ds))
Proof
  strip_tac >> gvs[heap_ok_def] >>
  simp[nodes_ok_def, listTheory.EVERY_MEM, MEM_alloc_list, PULL_EXISTS,
       node_plus_8] >>
  rw[] >>
  FIRST [
    irule alloc_list_distinct >> simp[] >> NO_TAC,
    ‘w2n (base + n2w (16 * i + 16)) = w2n base + (16 * i + 16)’
      by (irule w2n_base_add >> simp[]) >> strip_tac >> gvs[] >> NO_TAC,
    first_x_assum (qspec_then ‘2 * i + 2’ mp_tac) >>
      simp[arithmeticTheory.LEFT_ADD_DISTRIB] >> NO_TAC,
    first_x_assum (qspec_then ‘2 * i + 3’ mp_tac) >>
      simp[arithmeticTheory.LEFT_ADD_DISTRIB] >> NO_TAC,
    intLib.ARITH_TAC,
    simp[away_from_def, node_plus_8] >>
      ‘base = base + n2w 0 ∧ base + 8w = base + n2w 8’ by simp[] >>
      rpt conj_tac >> once_asm_rewrite_tac[] >> simp[base_add_11]]
QED

Theorem oom_check_false:
  heap_ok base tp dm n ∧ k < n ⇒
  ¬(tp − (base + n2w (16 * k + 16)) <₊ 16w)
Proof
  strip_tac >>
  qpat_x_assum ‘heap_ok _ _ _ _’ (strip_assume_tac o REWRITE_RULE [heap_ok_def]) >>
  ‘base + n2w (16 * k + 16) = n2w (w2n base + (16 * k + 16))’
    by simp[wordsTheory.word_add_def] >>
  ‘w2n base + (16 * k + 16) ≤ w2n tp’ by simp[] >>
  ‘tp − n2w (w2n base + (16 * k + 16)) =
   n2w (w2n tp − (w2n base + (16 * k + 16)))’
    by (qspecl_then [‘w2n tp’, ‘w2n base + (16 * k + 16)’] mp_tac
          (INST_TYPE [alpha |-> “:64”] wordsTheory.n2w_sub) >>
        asm_rewrite_tac [wordsTheory.n2w_w2n] >> disch_then (ACCEPT_TAC o SYM)) >>
  asm_rewrite_tac [wordsTheory.WORD_LO, wordsTheory.w2n_n2w] >>
  ‘w2n tp < dimword (:64)’ by simp[wordsTheory.w2n_lt] >>
  gvs[]
QED

(* ------------------------------------------------------------------------
   The two-word get_num buffer
   ------------------------------------------------------------------------ *)

Theorem aligned_plus_8:
  aligned 3 (a:word64) ⇒ aligned 3 (a + 8w)
Proof
  rw[alignmentTheory.aligned_bitwise_and] >> blastLib.FULL_BBLAST_TAC
QED

Theorem aligned_byte_align:
  aligned 3 (a:word64) ⇒ byte_align a = a ∧ byte_index a F = 0
Proof
  strip_tac >> drule aligned_offset >>
  disch_then (qspec_then ‘0’ mp_tac) >> simp[]
QED

Theorem mem_load_byte_aligned0:
  aligned 3 (a:word64) ∧ a ∈ dm ⇒
  mem_load_byte m dm F a = SOME (w2w (theWord (m a)))
Proof
  strip_tac >> drule aligned_offset >>
  disch_then (qspec_then ‘0’ mp_tac) >> simp[] >> strip_tac >>
  Cases_on ‘m a’ >> simp[mem_load_byte_def, get_byte_def, theWord_def]
QED

Theorem read_buffer9:
  aligned 3 (a:word64) ∧ a ∈ dm ∧ a + 8w ∈ dm ∧ m a = Word 0w ∧
  m (a + 8w) = Word 0w ⇒
  read_bytearray a 9 (mem_load_byte m dm F) = SOME (REPLICATE 9 0w)
Proof
  strip_tac >>
  ‘∀k. k < 8 ⇒ mem_load_byte m dm F (a + n2w k) = SOME 0w’
    by (rw[] >> drule_all mem_load_byte_aligned >> simp[get_byte_def]) >>
  ‘mem_load_byte m dm F a = SOME 0w’
    by (first_x_assum (qspec_then ‘0’ mp_tac) >> simp[]) >>
  ‘mem_load_byte m dm F (a + 8w) = SOME 0w’
    by (drule aligned_plus_8 >> strip_tac >> drule_all mem_load_byte_aligned0 >>
        simp[theWord_def]) >>
  rewrite_tac [EVAL “read_bytearray (a:word64) 9 f”] >>
  simp[GSYM wordsTheory.WORD_ADD_ASSOC, wordsTheory.word_add_n2w] >> EVAL_TAC
QED

Theorem write_buffer9:
  aligned 3 (a:word64) ∧ a ∈ dm ∧ a + 8w ∈ dm ∧ m (a + 8w) = Word 0w ⇒
  write_bytearray a (word_to_bytes w F ++ [b]) m dm F =
    (a =+ Word w) ((a + 8w =+ Word (w2w b)) m)
Proof
  strip_tac >> simp[write_bytearray_word] >>
  drule aligned_plus_8 >> strip_tac >>
  drule_all write_bytearray_one_byte >> simp[]
QED

Theorem replicate9_bytes:
  REPLICATE 9 (0w:word8) = word_to_bytes (0w:word64) F ++ [0w]
Proof
  EVAL_TAC
QED

(* ------------------------------------------------------------------------
   read_list
   ------------------------------------------------------------------------ *)
val rl_thms = [read_buffer9, write_buffer9, replicate9_bytes, ffiTheory.call_FFI_def,
               qs_oracle_def, miscTheory.read_bytearray_def, LET_THM,
               mem_load_byte_aligned0, aligned_plus_8, theWord_def,
               combinTheory.APPLY_UPDATE_THM, byteTheory.LENGTH_word_to_bytes];
val rl_thms2 = rl_thms @ [aligned_byte_align, byteTheory.get_byte_def, heap_form];
val rl_thms3 = rl_thms2 @ [ne_plus_8];

val modtac =
  ‘16 * LENGTH g + 24 < 18446744073709551616’ by (fs[] >> decide_tac) >>
  ‘16 * i + 24 < 18446744073709551616’ by decide_tac >>
  ‘16 * LENGTH g + 16 < 18446744073709551616 ∧ 16 * i + 16 < 18446744073709551616’
    by decide_tac >>
  simp[arithmeticTheory.LESS_MOD];

val base_every_tac = fn x =>
  qpat_assum ‘∀x. x = s.base_addr ∨ _ ⇒ _’ (qspec_then x mp_tac) >> simp[];
val hp_every_tac = fn x =>
  qpat_assum ‘∀x. x = hp ∨ _ ⇒ _’ (qspec_then x mp_tac) >> simp[];

val read_list_tac =
  rpt gen_tac >> simp[fun_spec_def, qsort_code_lookups] >> rpt strip_tac >> fs[] >>
  rewrite_tac [read_list_body_def] >> steps_tac >>
  (let val (inv, var) = loop "read_list" 0 in while_tac inv var end) >>
  TRY (qexists_tac ‘[]’ >>
       simp[same_frame_def, finite_mapTheory.FLOOKUP_UPDATE, alloc_list_nil, lseg_def] >>
       NO_TAC) >>
  ‘s.base_addr ∈ s.memaddrs ∧ s.base_addr + 8w ∈ s.memaddrs ∧ aligned 3 s.base_addr’
    by (fs[heap_ok_def] >> first_assum (qspec_then ‘0’ mp_tac) >>
        first_x_assum (qspec_then ‘1’ mp_tac) >> simp[]) >>
  rpt gen_tac >> strip_tac >> gvs[same_frame_def] >> simp eval_simps >> steps_tac >>
  asimp rl_thms >> Cases_on ‘s'.ffi.ffi_state’ >> asimp rl_thms
  >- ((* end of input: leave the loop and return the list *)
      steps_with rl_thms2 >>
      ‘g = s.ffi.ffi_state’ by (qpat_x_assum ‘g ++ _ = _’ mp_tac >> simp[]) >>
      conj_tac
      >- simp[state_component_equality, ffiTheory.ffi_state_component_equality] >>
      qexists_tac ‘alloc_list s.base_addr g’ >>
      ‘nodes_ok s.memaddrs (MAP FST (alloc_list s.base_addr g)) ∧
       EVERY (away_from s.base_addr) (MAP FST (alloc_list s.base_addr g))’
        by (irule alloc_list_ok >>
            qexistsl_tac [‘LENGTH s.ffi.ffi_state’, ‘s.top_addr’] >> gvs[]) >>
      simp[MAP_SND_alloc_list, get_ev_def, replicate9_bytes,
           ffiTheory.ffi_state_component_equality, sortingTheory.PERM_REVERSE] >>
      ‘∀x. (x = s.base_addr ∨ x = s.base_addr + 8w) ⇒
           EVERY (λa. x ≠ a ∧ x ≠ a + 8w) (MAP FST (alloc_list s.base_addr g))’
        by (rw[] >> gvs[listTheory.EVERY_MEM, away_from_def] >>
            metis_tac[wordsTheory.WORD_EQ_ADD_RCANCEL]) >>
      qpat_x_assum ‘g = _’ (fn th => REWRITE_TAC [GSYM th]) >>
      irule lseg_update >> conj_tac >- base_every_tac ‘s.base_addr’ >>
      irule lseg_update >> conj_tac >- base_every_tac ‘s.base_addr + 8w’ >>
      irule lseg_update >> conj_tac >- base_every_tac ‘s.base_addr’ >>
      first_assum ACCEPT_TAC)
  >- ((* read a number h: allocate a node for it *)
      ‘LENGTH g < LENGTH s.ffi.ffi_state’
        by (qpat_x_assum ‘g ++ _ = _’ (fn th => REWRITE_TAC [GSYM th]) >> simp[]) >>
      fs[heap_form] >>
      qabbrev_tac ‘hp = s.base_addr + n2w (16 * LENGTH g + 16)’ >>
      ‘hp ∈ s.memaddrs ∧ hp + 8w ∈ s.memaddrs’
        by (qpat_x_assum ‘heap_ok _ _ _ _’
              (strip_assume_tac o REWRITE_RULE [heap_ok_def]) >>
            qunabbrev_tac ‘hp’ >> REWRITE_TAC [node_plus_8] >>
            ‘16 * LENGTH g + 16 = 8 * (2 * LENGTH g + 2) ∧
             16 * LENGTH g + 24 = 8 * (2 * LENGTH g + 3)’ by decide_tac >>
            asm_rewrite_tac[] >> conj_tac >> first_x_assum irule >> decide_tac) >>
      ‘FLOOKUP s'.locals «heap» = SOME (ValWord hp)’
        by (qpat_x_assum ‘FLOOKUP _ «heap» = _’ mp_tac >> simp[Abbr ‘hp’] >>
            metis_tac[wordsTheory.WORD_ADD_COMM]) >>
      qpat_x_assum ‘FLOOKUP _ «heap» = SOME (ValWord (_ + _))’ kall_tac >>
      ‘¬(s.top_addr − hp <₊ 16w)’
        by (qunabbrev_tac ‘hp’ >> irule oom_check_false >> metis_tac[]) >>
      pop_assum (assume_tac o SIMP_RULE (srw_ss()) []) >>
      steps_with rl_thms2 >> asimp rl_thms3 >> steps_with rl_thms3 >>
      qexists_tac ‘g ++ [h]’ >> simp[get_ev_def, replicate9_bytes, alloc_list_snoc] >>
      conj_tac
      >- (qunabbrev_tac ‘hp’ >>
          ‘n2w (16 * (LENGTH g + 1) + 16) = n2w (16 * LENGTH g + 16) + (16w:word64)’
            by (REWRITE_TAC [wordsTheory.word_add_n2w] >> AP_TERM_TAC >> simp[]) >>
          pop_assum SUBST1_TAC >>
          metis_tac[wordsTheory.WORD_ADD_COMM, wordsTheory.WORD_ADD_ASSOC]) >>
      ‘nodes_ok s.memaddrs (MAP FST (alloc_list s.base_addr g)) ∧
       EVERY (away_from s.base_addr) (MAP FST (alloc_list s.base_addr g))’
        by (irule alloc_list_ok >>
            qexistsl_tac [‘LENGTH s.ffi.ffi_state’, ‘s.top_addr’] >> gvs[]) >>
      ‘∀x. x = hp ∨ x = hp + 8w ⇒
           EVERY (λa. x ≠ a ∧ x ≠ a + 8w) (MAP FST (alloc_list s.base_addr g))’
        by (qpat_x_assum ‘heap_ok _ _ _ _’
              (strip_assume_tac o REWRITE_RULE [heap_ok_def]) >>
            rw[listTheory.EVERY_MEM, MEM_alloc_list] >> qunabbrev_tac ‘hp’ >>
            simp[node_plus_8] >>
            rpt (TRY (simp[n2w_plus_8]) >> modtac >> TRY (simp[] >> NO_TAC))) >>
      ‘∀x. x = s.base_addr ∨ x = s.base_addr + 8w ⇒
           EVERY (λa. x ≠ a ∧ x ≠ a + 8w) (MAP FST (alloc_list s.base_addr g))’
        by (rw[] >> gvs[listTheory.EVERY_MEM, away_from_def] >>
            metis_tac[wordsTheory.WORD_EQ_ADD_RCANCEL]) >>
      simp[lseg_def, combinTheory.APPLY_UPDATE_THM, ne_plus_8] >>
      irule lseg_update >> conj_tac >- hp_every_tac ‘hp + 8w’ >>
      irule lseg_update >> conj_tac >- hp_every_tac ‘hp’ >>
      irule lseg_update >> conj_tac >- base_every_tac ‘s.base_addr’ >>
      irule lseg_update >> conj_tac >- base_every_tac ‘s.base_addr + 8w’ >>
      irule lseg_update >> conj_tac >- base_every_tac ‘s.base_addr’ >>
      first_assum ACCEPT_TAC);

val read_list_spec = store_thm ("read_list_spec", goal_of "read_list", read_list_tac);
