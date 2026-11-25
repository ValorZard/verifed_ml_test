(* Proof of the read_list contract (also included in panQsortProofScript.sml). *)
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
