(*
  Contract extraction for Pancake.

  Reads a .pnk file, parses it with Pancake's own (verified) parser inside
  the logic, and turns the contract annotations /@ ... @/ found in function
  bodies into HOL4 terms:

    requires: P        ↦  precondition   λvs s. ...
    ensures:  Q        ↦  postcondition  λvs s result mem' ffi'. ...
    invariant [g..]: I ↦  loop invariant λ(g..) s. (locals in scope) ∧ I
    decreases: e       ↦  loop variant   λ(g..) s. e

  The contract bodies are HOL4 terms (ASCII syntax).  Pancake variables
  denote their (word) values; mem, dom, ffi, base, top, be denote parts of
  the current state; result/mem'/ffi' the outcome (ensures); mem0/ffi0 the
  state on function entry (invariants).  Other free variables are ghosts.

  fun_spec_goal builds the proof obligation of a function contract.
*)
structure panContractLib =
struct

open HolKernel Parse boolLib bossLib

val ERR = mk_HOL_ERR "panContractLib"

fun read_file fname =
  let val i = TextIO.openIn fname
      val s = TextIO.inputAll i
  in TextIO.closeIn i; s end

(* ---------------------------------------------------------------------- *)
(* Parsing the Pancake program with the in-logic Pancake parser           *)
(* ---------------------------------------------------------------------- *)

fun parse_pancake_file fname =
  let
    val code = stringSyntax.fromMLstring (read_file fname)
    val parse = prim_mk_const {Thy = "panPtreeConversion",
                               Name = "parse_topdecs_to_ast"}
    val th = EVAL (mk_comb (parse, code))
    val r = rhs (concl th)
  in
    if sumSyntax.is_inl r then (fst (sumSyntax.dest_inl r), th)
    else raise ERR "parse_pancake_file" ("Pancake parse error:\n" ^ term_to_string r)
  end

(* ---------------------------------------------------------------------- *)
(* Walking the AST                                                        *)
(* ---------------------------------------------------------------------- *)

fun cname t = fst (dest_const (fst (strip_comb t))) handle HOL_ERR _ => ""
fun cargs t = snd (strip_comb t)
fun mlstr t = stringSyntax.fromHOLstring (rand t)   (* strlit "..." *)

(* A loop, with the variables in scope at the loop and those of them that
   the loop body assigns to. *)
datatype item = Ann of string | Loop of string list * string list

(* Local variables assigned (x = e) anywhere in a statement.  (Missing an
   assignment can only make an invariant unprovable, never unsound.) *)
fun assigned t =
  case (cname t, cargs t) of
    ("Assign", [_, x, _]) => [mlstr x]
  | (_, args) => List.concat (map assigned args)

(* Items in program order: annotations, and loops. *)
fun walk scope t acc =
  case (cname t, cargs t) of
    ("Seq", [a, b])           => walk scope b (walk scope a acc)
  | ("Dec", [x, _, _, p])     => walk (mlstr x :: scope) p acc
  | ("DecCall", [x, _, _, _, p]) => walk (mlstr x :: scope) p acc
  | ("If", [_, a, b])         => walk scope b (walk scope a acc)
  | ("While", [_, c])         => walk scope c (Loop (scope, assigned c) :: acc)
  | ("Annot", [k, s])         => if mlstr k = "@" then Ann (mlstr s) :: acc
                                 else acc
  | _ => acc

fun items_of params body = List.rev (walk (List.rev params) body [])

(* ---------------------------------------------------------------------- *)
(* Contract text                                                          *)
(* ---------------------------------------------------------------------- *)

fun trim s =
  Substring.string (Substring.dropr Char.isSpace
                      (Substring.dropl Char.isSpace (Substring.full s)))

(* "kw [g1 g2]: body"  ↦  (kw, [g1,g2], body) *)
fun split_annot s =
  let
    val (head, rest) = Substring.splitl (fn c => c <> #":") (Substring.full (trim s))
    val body = trim (Substring.string (Substring.triml 1 rest))
    val (kw, gs) = Substring.splitl (fn c => c <> #"[") head
    val ghosts =
      String.tokens (fn c => Char.isSpace c orelse c = #"[" orelse c = #"]")
                    (Substring.string gs)
  in (trim (Substring.string kw), ghosts, body) end

val state_ty = "(64, word64 list) panSem$state"
fun commas xs = String.concatWith "; " xs
fun conjs [] = "T" | conjs xs = String.concatWith " /\\ " xs

fun env_let s extra =
  "let mem = " ^ s ^ ".memory; dom = " ^ s ^ ".memaddrs; ffi = " ^ s ^
  ".ffi; base = " ^ s ^ ".base_addr; top = " ^ s ^ ".top_addr; be = " ^ s ^
  ".be" ^ extra ^ " in "

fun bind_params ps =
  if null ps then "vs = [] /\\ "
  else "?" ^ String.concatWith " " ps ^ ". vs = [" ^ commas ps ^ "] /\\ "

fun parse s = Term [QUOTE s]
  handle e => raise ERR "contract" ("cannot parse contract term:\n" ^ s ^
                                    "\n" ^ General.exnMessage e)

(* The pieces of a contract are produced as strings and parsed together in
   one term, so that a ghost variable gets the same type everywhere. *)
fun pre_str params body =
  "\\(vs:word64 list) (s:" ^ state_ty ^ "). " ^ bind_params params ^
  "(" ^ env_let "s" "" ^ "(" ^ body ^ "))"

fun post_str params body =
  "\\(vs:word64 list) (s:" ^ state_ty ^ ") (result:word64) " ^
  "(mem':word64 -> 64 panSem$word_lab) (ffi':word64 list ffi_state). " ^
  bind_params params ^ "(" ^ env_let "s" "" ^ "(" ^ body ^ "))"

fun ghost_pat [] = "(u:unit)"
  | ghost_pat [g] = g
  | ghost_pat gs = "(" ^ String.concatWith "," gs ^ ")"

val entry_env = "; mem0 = s0.memory; ffi0 = s0.ffi"

(* Variables in scope that the loop assigns are existentially quantified;
   the others keep their values, so they are left free and instantiated
   with their current values when the loop rule is applied (while_tac). *)
fun inv_str (scope, asgd) ghosts body =
  let
    val locals = map (fn v => "FLOOKUP s.locals (strlit \"" ^ v ^
                              "\") = SOME (ValWord " ^ v ^ ")") scope
    val exvars = List.filter (fn v => List.exists (fn a => a = v) asgd) scope
    val ex = if null exvars then "" else "?" ^ String.concatWith " " exvars ^ ". "
  in
    "\\" ^ ghost_pat ghosts ^ " (s:" ^ state_ty ^ "). " ^ ex ^
    conjs (locals @ ["same_frame (s0:" ^ state_ty ^ ") s"]) ^
    " /\\ (" ^ env_let "s" entry_env ^ "(" ^ body ^ "))"
  end

fun var_str (scope, _) ghosts body =
  let
    val lets = map (fn v => v ^ " = lv s (strlit \"" ^ v ^ "\")") scope
  in
    "\\" ^ ghost_pat ghosts ^ " (s:" ^ state_ty ^ "). let " ^
    String.concatWith "; " (lets @ ["mem = s.memory; dom = s.memaddrs; ffi = s.ffi; base = s.base_addr; top = s.top_addr; be = s.be" ^ entry_env]) ^
    " in ((" ^ body ^ ") : num)"
  end

(* ---------------------------------------------------------------------- *)
(* Contracts of a whole program                                           *)
(* ---------------------------------------------------------------------- *)

type loop_contract = {inv : term, var : term}
type contract = {name : string, params : string list,
                 pre : term, post : term, loops : loop_contract list}

fun contract_of (name, params, body) : contract =
  let
    val items = items_of params body
    fun find kw = List.mapPartial
                    (fn Ann s => let val (k, g, b) = split_annot s
                                 in if k = kw then SOME b else NONE end
                      | _ => NONE) items
    fun one kw = case find kw of [b] => b | [] => "T"
                   | _ => raise ERR "contract_of" (name ^ ": several " ^ kw)
    (* attach invariant/decreases annotations to the next loop *)
    fun loops [] _ = []
      | loops (Ann s :: rest) pending = loops rest (split_annot s :: pending)
      | loops (Loop scope :: rest) pending =
          let
            val inv = List.find (fn (k, _, _) => k = "invariant") pending
            val var = List.find (fn (k, _, _) => k = "decreases") pending
          in
            case (inv, var) of
              (SOME (_, gs, ib), SOME (_, _, vb)) =>
                (inv_str scope gs ib, var_str scope gs vb) :: loops rest []
            | _ => raise ERR "contract_of"
                     (name ^ ": loop without invariant and decreases annotations")
          end
    val loop_strs = loops items []
    val strs = [pre_str params (one "requires"), post_str params (one "ensures")] @
               List.concat (map (fn (i, v) => [i, v]) loop_strs)
    val tm = parse ("(" ^ String.concatWith ",\n" (map (fn x => "(" ^ x ^ ")") strs) ^ ")")
    val parts = pairSyntax.strip_pair tm
    (* the variant's ghost pattern is bound separately from the invariant's;
       give it the invariant's ghost type *)
    fun align v i =
      inst (match_type (fst (dom_rng (type_of v))) (fst (dom_rng (type_of i)))) v
      handle HOL_ERR _ => v
    fun pairs (i :: v :: rest) = {inv = i, var = align v i} :: pairs rest
      | pairs _ = []
  in
    {name = name, params = params, pre = List.nth (parts, 0),
     post = List.nth (parts, 1), loops = pairs (List.drop (parts, 2))}
  end

(* All functions of a parsed program: (name, param names, body). *)
fun functions_of decls =
  let
    val fs = rhs (concl (EVAL (mk_comb (prim_mk_const {Thy = "panLang",
                                                       Name = "functions"},
                                        decls))))
    fun one t =
      let val (n, rest) = pairSyntax.dest_pair t
          val (ps, rest) = pairSyntax.dest_pair rest
          val (body, _) = pairSyntax.dest_pair rest
          val pnames = map (mlstr o fst o pairSyntax.dest_pair)
                           (fst (listSyntax.dest_list ps))
      in (mlstr n, pnames, body) end
  in map one (fst (listSyntax.dest_list fs)) end

fun contracts_of decls = map contract_of (functions_of decls)

fun find_contract (cs : contract list) name =
  case List.find (fn c => #name c = name) cs of
    SOME c => c
  | NONE => raise ERR "find_contract" name

(* The proof obligation of a function contract, over the code map `code`:
   for all ghost variables, fun_spec code name params pre post. *)
fun fun_spec_goal code (c : contract) =
  let
    val params = listSyntax.mk_list
                   (map (fn p => mlstringSyntax.mk_mlstring p) (#params c),
                    mlstringSyntax.mlstring_ty)
    val nm = mlstringSyntax.mk_mlstring (#name c)
    val tm = boolSyntax.list_mk_icomb
               (prim_mk_const {Thy = "panLogic", Name = "fun_spec"},
                [code, nm, params, #pre c, #post c])
  in list_mk_forall (free_vars tm, tm) end

end
