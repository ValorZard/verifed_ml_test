(*
  Symbolic execution of Pancake code in `runs` goals.

  step_tac applies one rule of the program logic (panLogic) to a goal
  `runs p s P`, according to the shape of p:
    Seq        -> runs_Seq
    Dec        -> runs_Dec, evaluating the initialiser
    If         -> runs_If, evaluating the condition
    leaf stmt  -> runs_eval, computing the statement with panSem$evaluate
  It fails on While loops and calls, which are handled with the contract
  of the loop (while_tac) or of the callee (runs_*Call_spec).
*)
structure panStepLib =
struct

open HolKernel Parse boolLib bossLib

val ERR = mk_HOL_ERR "panStepLib"

val runs_tm = prim_mk_const {Thy = "panLogic", Name = "runs"}

fun cname t = fst (dest_const (fst (strip_comb t))) handle HOL_ERR _ => ""

fun runs_prog w =
  let val (c, args) = strip_comb w
  in if same_const c runs_tm then SOME (hd args) else NONE end

val eval_simps =
  [panSemTheory.eval_def, panSemTheory.mem_load_def,
   wordSemTheory.word_op_def, asmTheory.word_cmp_def,
   listTheory.OPT_MMAP_def,
   finite_mapTheory.FLOOKUP_UPDATE, finite_mapTheory.FUPDATE_LIST_THM,
   finite_mapTheory.DOMSUB_FLOOKUP_THM,
   panSemTheory.shape_of_def, panSemTheory.flatten_def,
   panSemTheory.mem_stores_def, panSemTheory.mem_store_def,
   panSemTheory.is_valid_value_def, panSemTheory.lookup_kvar_def,
   panSemTheory.set_kvar_def, panSemTheory.set_var_def,
   panSemTheory.empty_locals_def, panSemTheory.res_var_def,
   panSemTheory.mem_load_byte_def, panSemTheory.mem_store_byte_def,
   combinTheory.APPLY_UPDATE_THM,
   panLangTheory.size_of_sh_with_ctxt_def, panLangTheory.is_wf_shape_def,
   integer_wordTheory.i2w_pos, EVAL “i2w 0 : word64”]

(* simplification that may use the assumptions *)
fun asimp thms = asm_simp_tac (srw_ss()) thms

fun step_with thms : tactic = fn (g as (_, w)) =>
  case runs_prog w of
    NONE => raise ERR "step_tac" "not a runs goal"
  | SOME p =>
    (case cname p of
       "Seq" => irule panLogicTheory.runs_Seq
     | "Dec" => irule panLogicTheory.runs_Dec >> asimp (eval_simps @ thms)
     | "If" => irule panLogicTheory.runs_If >> asimp (eval_simps @ thms)
     | "COND" => IF_CASES_TAC >> asimp thms
     | "While" => raise ERR "step_tac" "loop"
     | "Call" => raise ERR "step_tac" "call"
     | "DecCall" => raise ERR "step_tac" "call"
     | _ => irule panLogicTheory.runs_eval >>
            asimp (panSemTheory.evaluate_def :: eval_simps @ thms)) g

val step_tac = step_with []

(* Run step_tac until it no longer applies. *)
fun steps_with thms = rpt (step_with thms)
val steps_tac = steps_with []

(* Apply the loop rule with the given invariant and variant (as produced by
   panContractLib, with the function-entry state s0 instantiated).  Leaves
   two goals: the loop body preserves the invariant, and it holds on entry. *)
fun while_tac inv var : tactic = fn (g as (_, w)) =>
  let
    (* goal: runs (While e c) s P; free variables of the invariant that name
       local variables the loop does not assign get their current values *)
    val s = hd (tl (snd (strip_comb w)))
    fun value_of v =
      let
        val n = mlstringSyntax.mk_mlstring (fst (dest_var v))
        val r = rhs (concl (EVAL “FLOOKUP ^s.locals ^n”))
        val t = rand (rand (rand r))             (* SOME (Val (Word t)) *)
      in if type_of t = type_of v then SOME (v |-> t) else NONE end
      handle HOL_ERR _ => NONE
    val sub = List.mapPartial value_of (free_vars inv)
  in
    (MATCH_MP_TAC (ISPECL [subst sub inv, subst sub var]
                          panLogicTheory.runs_While_inv) >> conj_tac) g
  end

(* Instantiate the entry state s0 of a loop contract. *)
fun loop_contract_at (lc : {inv : term, var : term}) s =
  let
    val s0 = mk_var ("s0", type_of s)
  in
    (subst [s0 |-> s] (#inv lc), subst [s0 |-> s] (#var lc))
  end

val i2w_simps = [integer_wordTheory.i2w_pos, EVAL “i2w 0 : word64”]

end
