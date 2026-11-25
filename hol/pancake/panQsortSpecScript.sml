(*
  Vocabulary used in the contracts of qsort.pnk:
    - linked-list segments in Pancake memory (separation by explicit
      disjointness side conditions),
    - the memory layout used by the program,
    - the FFI oracle the C glue implements, and the I/O events it produces.
*)
Theory panQsortSpec
Ancestors
  panSem panLogic sorting
Libs
  preamble

Type pan_state = “:(64, word64 list) panSem$state”

(* lseg m xs p q: memory m holds a list segment from pointer p to pointer q
   whose nodes are FST xs (each node a = [value; next] at a, a + 8) and
   whose values are SND xs. *)
Definition lseg_def:
  (lseg (m: word64 -> 64 panSem$word_lab) [] p q ⇔ p = q) ∧
  (lseg m ((a,v)::xs) p q ⇔
     p = a ∧ m a = panSem$Word v ∧ ∃n. m (a + 8w) = panSem$Word n ∧ lseg m xs n q)
End

(* Node addresses are distinct, non-null, inside memory, and no node's value
   field is another node's next field. *)
Definition nodes_ok_def:
  nodes_ok dom (as: word64 list) ⇔
    ALL_DISTINCT as ∧
    ∀a. MEM a as ⇒ a ≠ 0w ∧ a ∈ dom ∧ a + 8w ∈ dom ∧
                   ∀b. MEM b as ⇒ a ≠ b + 8w
End

(* Only the next fields of the nodes as may differ between m and m'. *)
Definition frame_def:
  frame (as: word64 list) (m: word64 -> 64 panSem$word_lab) m' ⇔
    ∀a. (∀b. MEM b as ⇒ a ≠ b + 8w) ⇒ m' a = m a
End

(* Order on (node, value) pairs: by value, signed. *)
Definition val_le_def:
  val_le (a:word64, v:word64) (b:word64, w:word64) ⇔ v ≤ w
End

(* Node a does not overlap the two-word I/O buffer at base. *)
Definition away_from_def:
  away_from (base:word64) a ⇔ a ≠ base ∧ a + 8w ≠ base ∧ a ≠ base + 8w
End

(* Enough memory for the I/O buffer and n nodes, without wrap-around. *)
Definition heap_ok_def:
  heap_ok (base:word64) (top:word64) dom n ⇔
    aligned 3 base ∧
    w2n base + 16 * n + 16 < dimword (:64) ∧
    w2n base + 16 * n + 16 ≤ w2n top ∧
    ∀i. i < 2 * n + 2 ⇒ base + n2w (8 * i) ∈ dom
End

(* The list built by read_list after reading done: node i is at
   base + 16 + 16 i, and the newest node is the head. *)
Definition alloc_list_def:
  alloc_list (base:word64) (done: word64 list) =
    REVERSE (MAPi (λi v. (base + 16w + n2w (16 * i), v)) done)
End

(* ------------------------------------------------------------------------
   FFI model (implemented by qsort_ffi.c)
   ------------------------------------------------------------------------ *)

Definition qs_oracle_def:
  qs_oracle (ffi$ExtCall n) (inp: word64 list) (conf: word8 list) (bytes: word8 list) =
    (if n = «get_num» ∧ LENGTH bytes = 9 then
       (case inp of
          [] => Oracle_return [] (REPLICATE 9 0w)
        | w::ws => Oracle_return ws (word_to_bytes w F ++ [1w]))
     else if n = «put_num» ∧ LENGTH bytes = 8 then Oracle_return inp bytes
     else Oracle_final FFI_failed) ∧
  qs_oracle _ inp conf bytes = Oracle_final FFI_failed
End

Definition get_ev_def:
  get_ev (NONE: word64 option) =
    IO_event (ffi$ExtCall «get_num») [] (ZIP (REPLICATE 9 0w, REPLICATE 9 0w)) ∧
  get_ev (SOME w) =
    IO_event (ffi$ExtCall «get_num») [] (ZIP (REPLICATE 9 0w, word_to_bytes w F ++ [1w]))
End

Definition put_ev_def:
  put_ev (w: word64) =
    IO_event (ffi$ExtCall «put_num») [] (ZIP (word_to_bytes w F, word_to_bytes w F))
End
