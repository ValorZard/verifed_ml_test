(*
  The Pancake program qsort.pnk inside HOL4.

  - qsort_parses: Pancake's (in-logic) parser, applied to the exact text of
    qsort.pnk, produces the AST qsort_decls.  The compiler binary uses the
    same parser, so it compiles exactly this AST.
  - qsort_code: the function table that Pancake's semantics installs.
  - Byte-level lemmas relating the 8-byte FFI buffers to memory words.
*)
Theory panQsortProg
Ancestors
  panQsortSpec panLogic panSem panProps panLang panPtreeConversion
  byte alignment misc words
Libs
  preamble panContractLib blastLib

(* ------------------------------------------------------------------------
   The program
   ------------------------------------------------------------------------ *)

val source_text = panContractLib.read_file "qsort.pnk";
val (decls_tm, parse_thm) = panContractLib.parse_pancake_file "qsort.pnk";

val qsort_source_def = new_definition ("qsort_source_def",
  boolSyntax.mk_eq (Term.mk_var ("qsort_source", stringSyntax.string_ty),
         stringSyntax.fromMLstring source_text));

val qsort_decls_def = new_definition ("qsort_decls_def",
  boolSyntax.mk_eq (Term.mk_var ("qsort_decls", type_of decls_tm), decls_tm));

val _ = computeLib.add_funs [qsort_decls_def];

Theorem qsort_parses:
  parse_topdecs_to_ast qsort_source = INL qsort_decls
Proof
  rewrite_tac [qsort_source_def, qsort_decls_def, parse_thm]
QED

(* The function bodies, as named constants (keeps goals readable). *)
val funs = panContractLib.functions_of decls_tm;
val body_defs = map (fn (name, _, body) =>
  new_definition (name ^ "_body_def",
    boolSyntax.mk_eq (Term.mk_var (name ^ "_body", type_of body), body))) funs;

Theorem qsort_functions =
  EVAL “functions qsort_decls”
  |> REWRITE_RULE (map GSYM body_defs) |> PURE_REWRITE_RULE [GSYM qsort_decls_def];

Definition qsort_code_def:
  qsort_code =
    FEMPTY |++ MAP (λ(n,ps,b,r). (n,(ps,b,r))) (functions qsort_decls)
End

(* Pancake's declaration semantics installs exactly qsort_code. *)
Theorem qsort_decs_stcnames:
  decs_stcnames [] qsort_decls = SOME []
Proof
  rewrite_tac [qsort_decls_def] >> EVAL_TAC
QED

Theorem evaluate_decls_qsort:
  s.code = FEMPTY ⇒
  evaluate_decls (s with structs := []) qsort_decls =
    SOME (s with <| structs := []; code := qsort_code |>)
Proof
  strip_tac >>
  simp [qsort_decls_def, evaluate_decls_def, is_wf_shape_def, qsort_code_def,
        functions_def, FUPDATE_LIST_THM] >>
  simp [panSemTheory.state_component_equality]
QED

Theorem qsort_code_lookups =
  map (fn (name, _, _) =>
         let val n = mlstringSyntax.mk_mlstring name
         in EVAL “FLOOKUP qsort_code ^n” end
         |> REWRITE_RULE (map GSYM body_defs)) funs
  |> LIST_CONJ;

(* ------------------------------------------------------------------------
   Byte-level lemmas for the 8-byte FFI buffers (little-endian, be = F)
   ------------------------------------------------------------------------ *)

Theorem w2n_MOD_8:
  w2n (x:word64) MOD 8 = w2n (x && 7w)
Proof
  assume_tac (WORD_AND_EXP_SUB1 |> INST_TYPE [alpha |-> “:64”]
              |> Q.SPECL [‘3’, ‘w2n (x:word64)’] |> SIMP_RULE (srw_ss()) [n2w_w2n]) >>
  ONCE_REWRITE_TAC [WORD_AND_COMM] >> asm_rewrite_tac[] >>
  ‘w2n x MOD 8 < 8’ by simp[] >> simp[w2n_n2w]
QED

Theorem aligned_and_7:
  aligned 3 (a:word64) ∧ k < 8 ⇒
  7w && (a + n2w k) = n2w k ∧ 0xFFFFFFFFFFFFFFF8w && (a + n2w k) = a ∧
  (a + n2w k) && 7w = n2w k
Proof
  rw[aligned_bitwise_and] >>
  ‘k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7’ by decide_tac >>
  gvs[] >> blastLib.FULL_BBLAST_TAC
QED

Theorem aligned_offset:
  aligned 3 (a:word64) ∧ k < 8 ⇒
  byte_align (a + n2w k) = a ∧ byte_index (a + n2w k) F = 8 * k
Proof
  strip_tac >> drule_all aligned_and_7 >> strip_tac >>
  simp[byte_align_def, align_bitwise_and, byte_index_def, w2n_MOD_8]
QED

Theorem mem_load_byte_aligned:
  aligned 3 (a:word64) ∧ a ∈ dm ∧ m a = Word w ∧ k < 8 ⇒
  mem_load_byte m dm F (a + n2w k) = SOME (get_byte (n2w k) w F)
Proof
  strip_tac >> drule_all aligned_offset >> strip_tac >>
  simp[mem_load_byte_def, get_byte_def, byte_index_def]
QED

Theorem read_bytearray_word:
  aligned 3 (a:word64) ∧ a ∈ dm ∧ m a = Word w ⇒
  read_bytearray a 8 (mem_load_byte m dm F) = SOME (word_to_bytes w F)
Proof
  strip_tac >>
  ‘∀k. k < 8 ⇒ mem_load_byte m dm F (a + n2w k) = SOME (get_byte (n2w k) w F)’
    by metis_tac[mem_load_byte_aligned] >>
  ‘mem_load_byte m dm F a = SOME (get_byte 0w w F)’
    by (first_x_assum (qspec_then ‘0’ mp_tac) >> simp[]) >>
  rewrite_tac[EVAL “read_bytearray (a:word64) 8 f”] >>
  simp[GSYM WORD_ADD_ASSOC, word_add_n2w] >>
  simp[word_to_bytes_def, word_to_bytes_aux_def] >>
  CONV_TAC (RAND_CONV EVAL) >> simp[get_byte_def, byte_index_def]
QED

Theorem mem_store_byte_aligned:
  aligned 3 (a:word64) ∧ a ∈ dm ∧ k < 8 ⇒
  mem_store_byte m dm F (a + n2w k) b =
    SOME ((a =+ Word (set_byte (n2w k) b (theWord (m a)) F)) m)
Proof
  strip_tac >> drule_all aligned_offset >> strip_tac >>
  Cases_on ‘m a’ >>
  simp[mem_store_byte_def, set_byte_def, byte_index_def, theWord_def]
QED

Theorem set_byte_chain[local]:
  set_byte 0w (w2w (w:word64)) (set_byte 1w (w2w (w ⋙ 8)) (set_byte 2w (w2w (w ⋙ 16))
    (set_byte 3w (w2w (w ⋙ 24)) (set_byte 4w (w2w (w ⋙ 32)) (set_byte 5w (w2w (w ⋙ 40))
    (set_byte 6w (w2w (w ⋙ 48)) (set_byte 7w (w2w (w ⋙ 56)) (v:word64) F) F) F) F) F)
    F) F) F = w
Proof
  simp[set_byte_def, byte_index_def, word_slice_alt_def] >> blastLib.BBLAST_TAC
QED

Theorem write_bytearray_word:
  aligned 3 (a:word64) ∧ a ∈ dm ⇒
  write_bytearray a (word_to_bytes w F ++ rest) m dm F =
    (a =+ Word w) (write_bytearray (a + 8w) rest m dm F)
Proof
  strip_tac >>
  ‘∀k b m. k < 8 ⇒ mem_store_byte m dm F (a + n2w k) b =
             SOME ((a =+ Word (set_byte (n2w k) b (theWord (m a)) F)) m)’
    by metis_tac[mem_store_byte_aligned] >>
  ‘∀b m. mem_store_byte m dm F a b =
           SOME ((a =+ Word (set_byte 0w b (theWord (m a)) F)) m)’
    by (rpt gen_tac >> first_x_assum (qspecl_then [‘0’,‘b’,‘m’] mp_tac) >>
        simp[]) >>
  simp[word_to_bytes_def] >>
  rewrite_tac [EVAL “word_to_bytes_aux 8 (w:word64) F”, listTheory.APPEND] >>
  simp[write_bytearray_def, GSYM WORD_ADD_ASSOC, word_add_n2w] >>
  simp[theWord_def, set_byte_chain]
QED

(* The 9th byte of the get_num buffer, in a word that was zeroed. *)
Theorem write_bytearray_one_byte:
  aligned 3 (a:word64) ∧ a ∈ dm ∧ m a = Word 0w ⇒
  write_bytearray a [b] m dm F = (a =+ Word (w2w b)) m ∧
  get_byte a (w2w b : word64) F = b
Proof
  strip_tac >> drule aligned_offset >> disch_then (qspec_then ‘0’ mp_tac) >>
  simp[] >> strip_tac >> conj_tac
  >- (simp[write_bytearray_def, mem_store_byte_def, set_byte_def,
           word_slice_alt_def] >>
      ‘∀X Y. X = Y ⇒ (a =+ Word X) m = (a =+ Word Y) m’ by simp[] >>
      first_x_assum irule >> blastLib.BBLAST_TAC)
  >- (simp[get_byte_def] >> blastLib.BBLAST_TAC)
QED
