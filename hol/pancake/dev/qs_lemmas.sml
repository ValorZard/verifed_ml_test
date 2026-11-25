(* Lemmas for the qs proof (also included in panQsortProofScript.sml). *)

Theorem lseg_frame:
  ∀xs m m' p q. lseg m xs p q ∧
    (∀a. MEM a (MAP FST xs) ⇒ m' a = m a ∧ m' (a + 8w) = m (a + 8w)) ⇒
    lseg m' xs p q
Proof
  Induct >> simp[lseg_def, pairTheory.FORALL_PROD] >> rw[] >> metis_tac[]
QED

Theorem lseg_append:
  ∀xs ys m p q. lseg m (xs ++ ys) p q ⇔ ∃r. lseg m xs p r ∧ lseg m ys r q
Proof
  Induct >> simp[lseg_def, pairTheory.FORALL_PROD] >> metis_tac[]
QED

Theorem nodes_ok_PERM:
  PERM as bs ⇒ (nodes_ok dm as ⇔ nodes_ok dm bs)
Proof
  rw[nodes_ok_def] >>
  metis_tac[sortingTheory.ALL_DISTINCT_PERM, sortingTheory.MEM_PERM]
QED

Theorem nodes_ok_append:
  nodes_ok dm (as ++ bs) ⇔
    nodes_ok dm as ∧ nodes_ok dm bs ∧
    ∀a b. MEM a as ∧ MEM b bs ⇒ a ≠ b ∧ a ≠ b + 8w ∧ b ≠ a + 8w
Proof
  rw[nodes_ok_def, listTheory.ALL_DISTINCT_APPEND] >> metis_tac[]
QED

Theorem lseg_frame_disjoint:
  lseg m xs p q ∧ frame as m m' ∧
  (∀a b. MEM a (MAP FST xs) ∧ MEM b as ⇒ a ≠ b ∧ a ≠ b + 8w) ⇒
  lseg m' xs p q
Proof
  rw[frame_def] >> irule lseg_frame >> qexists_tac ‘m’ >> rw[] >>
  first_x_assum irule >> rw[] >> metis_tac[wordsTheory.WORD_EQ_ADD_RCANCEL]
QED

Theorem lseg_update_node:
  lseg m xs p q ∧ ¬MEM c (MAP FST xs) ∧
  (∀b. MEM b (MAP FST xs) ⇒ b ≠ c + 8w) ⇒
  lseg ((c + 8w =+ y) m) xs p q
Proof
  rw[] >> irule lseg_update >> gvs[listTheory.EVERY_MEM] >> rw[] >>
  metis_tac[wordsTheory.WORD_EQ_ADD_RCANCEL]
QED

Theorem frame_refl[simp]:
  frame as m m
Proof
  simp[frame_def]
QED

Theorem frame_trans:
  frame as m1 m2 ∧ frame bs m2 m3 ∧ (∀b. MEM b bs ⇒ MEM b as) ⇒ frame as m1 m3
Proof
  rw[frame_def] >> metis_tac[]
QED

Theorem frame_update:
  MEM c as ⇒ frame as m ((c + 8w =+ y) m)
Proof
  rw[frame_def, combinTheory.APPLY_UPDATE_THM] >> metis_tac[]
QED

Theorem frame_mono:
  frame as m m' ∧ (∀b. MEM b as ⇒ MEM b bs) ⇒ frame bs m m'
Proof
  rw[frame_def] >> metis_tac[]
QED

Theorem transitive_val_le:
  transitive val_le
Proof
  rw[relationTheory.transitive_def, pairTheory.FORALL_PROD, val_le_def] >>
  metis_tac[wordsTheory.WORD_LESS_EQ_TRANS]
QED
