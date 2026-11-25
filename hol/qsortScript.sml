(*
  Quicksort on lists of integers: definition and correctness proof.

  This theory is plain HOL4.  Everything that runs in the final binary is
  generated from the definitions here (and in qsortProg) by CakeML's
  proof-producing translator.
*)
Theory qsort
Ancestors
  list sorting integer
Libs
  preamble intLib

(* ------------------------------------------------------------------------
   The algorithm
   ------------------------------------------------------------------------ *)

Definition qsort_def:
  (qsort [] = []) ∧
  (qsort ((p:int)::xs) =
     qsort (FILTER (λx:int. x < p) xs) ++ [p] ++ qsort (FILTER (λx:int. p ≤ x) xs))
Termination
  WF_REL_TAC ‘measure LENGTH’ >> rw[] >>
  irule arithmeticTheory.LESS_EQ_IMP_LESS_SUC >> rw[LENGTH_FILTER_LEQ]
End

(* ------------------------------------------------------------------------
   Correctness: the result is a sorted permutation of the input
   ------------------------------------------------------------------------ *)

Theorem PERM_FILTER_lt_le[local]:
  ∀l (p:int). PERM (FILTER (λx:int. x < p) l ++ FILTER (λx:int. p ≤ x) l) l
Proof
  Induct >> rw[] >> gvs[integerTheory.INT_NOT_LT] >>
  TRY (drule_all integerTheory.INT_LTE_TRANS >> simp[] >> NO_TAC) >>
  simp[PERM_FUN_APPEND_CONS, PERM_CONS_IFF]
QED

Theorem qsort_PERM:
  ∀l. PERM (qsort l) l
Proof
  ho_match_mp_tac qsort_ind >> rw[qsort_def] >>
  REWRITE_TAC[GSYM APPEND_ASSOC, APPEND] >>
  simp[PERM_FUN_APPEND_CONS, PERM_CONS_IFF] >>
  irule PERM_TRANS >>
  qexists_tac ‘FILTER (λx. x < p) xs ++ FILTER (λx. p ≤ x) xs’ >>
  simp[PERM_FILTER_lt_le, PERM_CONG]
QED

Theorem MEM_qsort[simp]:
  ∀l x. MEM x (qsort l) ⇔ MEM x l
Proof
  metis_tac[MEM_PERM, qsort_PERM]
QED

Theorem LENGTH_qsort[simp]:
  ∀l. LENGTH (qsort l) = LENGTH l
Proof
  metis_tac[PERM_LENGTH, qsort_PERM]
QED

Theorem transitive_int_le[local]:
  transitive ($<= : int -> int -> bool)
Proof
  rw[relationTheory.transitive_def] >> intLib.ARITH_TAC
QED

Theorem qsort_SORTED:
  ∀l. SORTED $<= (qsort l)
Proof
  ho_match_mp_tac qsort_ind >> rw[qsort_def] >>
  simp[SORTED_APPEND, transitive_int_le, MEM_FILTER] >>
  rw[] >> intLib.ARITH_TAC
QED

(* A sorted permutation is unique, so qsort computes *the* sorted version of
   its input; e.g. it agrees with HOL's library sort QSORT. *)
Theorem qsort_unique:
  ∀l ys. SORTED $<= ys ∧ PERM ys l ⇒ qsort l = ys
Proof
  rw[] >> irule SORTED_PERM_EQ >>
  conj_tac >- metis_tac[qsort_PERM, PERM_TRANS, PERM_SYM] >>
  qexists_tac ‘$<=’ >>
  simp[transitive_int_le, qsort_SORTED, relationTheory.antisymmetric_def] >>
  intLib.ARITH_TAC
QED

Theorem qsort_eq_QSORT:
  ∀l. qsort l = QSORT $<= l
Proof
  gen_tac >> irule qsort_unique >>
  conj_tac
  >- metis_tac[QSORT_PERM, PERM_SYM]
  >- (irule QSORT_SORTED >>
      simp[relationTheory.total_def, relationTheory.transitive_def] >>
      intLib.ARITH_TAC)
QED
